import ComputationalSecurity.DistInd
import ComputationalSecurity.BVCryptGameLib
import ComputationalSecurity.PRG_impl_NB_Unpred
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

namespace ComputationalSecurity

open PMF
open BVCryptGame



variable {α : Type}

-- ============================================================
-- 1. アルゴリズムの構成 (既存スタイル通りの定義)
-- ============================================================

/-- 識別器 A を反転させた新しい識別器 -/
noncomputable def negate_distinguisher (A : α → PMF Bit) (x : α) : PMF Bit := do
  let a ← A x
  PMF.pure (if a == 1 then 0 else 1)

/-- 識別器 A から予測器 B を作る構成 -/
noncomputable def predictor_B (A : α × Bool → PMF Bit) (x : α) : PMF Bool := do
  let z ← PMF.uniformOfFintype Bool
  let a ← A (x, z)
  PMF.pure (if a == 1 then z else !z)

-- ============================================================
-- 2. アドバンテージと成功確率の再定義 (2引数・ジョイント分布版)
-- ============================================================

/-- ジョイント分布 X_joint における識別器 A のアドバンテージ。
    α は prefix の型 (BitVec i など) を指す。 -/
noncomputable def advantage {α : Type} (X_joint : PMF (α × Bool)) (A : α × Bool → PMF Bit) : ℝ :=
  PrDX_one X_joint A -
  PrDX_one (do let (x, _) ← X_joint; let u ← U 1; PMF.pure (x, u.getLsbD 0)) A

/-- ジョイント分布 X_joint における予測器 B の成功確率。 -/
noncomputable def prediction_success_prob {α : Type} (X_joint : PMF (α × Bool)) (B : α → PMF Bool) : ℝ :=
  (Pr (do
    let (x, p_x) ← X_joint
    let b ← B x
    PMF.pure (b == p_x)
  )).toReal

-- ============================================================
-- 3. 補題 4.2 (Prediction Lemma)
-- ============================================================

/-- 補題 4.2 の核心となる等式 -/
lemma predictor_B_success_eq_half_plus_adv {α : Type} (X_joint : PMF (α × Bool))
    (A : α × Bool → PMF Bit) :
    prediction_success_prob X_joint (predictor_B A) = 1 / 2 + advantage X_joint A := by
  unfold prediction_success_prob advantage PrDX_one
  rw [bind_assoc,bind_assoc,bind_assoc]

  -- 実数の等号を ENNReal の等号に持ち上げる

  have h_real_goal :
      (Pr (do let (x, p_x) ← X_joint; let b ← predictor_B A x; PMF.pure (b == p_x))).toReal
      + (Pr (do let (x, _) ← X_joint; let b ← PMF.uniformOfFintype Bool; let a ← A (x, b); PMF.pure (a == 1))).toReal
      = (1 / 2 : ℝ) + (Pr (do let (x, p_x) ← X_joint; let a ← A (x, p_x); PMF.pure (a == 1))).toReal := by

    -- ここなら 1/2 + ... という形が綺麗に ENNReal と対応する
    have h_enn : (Pr (do let (x, p_x) ← X_joint; let b ← predictor_B A x; PMF.pure (b == p_x)))
               + (Pr (do let (x, _) ← X_joint; let b ← PMF.uniformOfFintype Bool; let a ← A (x, b); PMF.pure (a == 1)))
               = (1 / 2 : ENNReal) + (Pr (do let (x, p_x) ← X_joint; let a ← A (x, p_x); PMF.pure (a == 1))) := by
      -- この have の中で U1_getLsbD_eq_uniformBool を適用して advantage の項と同期させる
      unfold predictor_B
      simp only [bind_assoc, Fin.isValue]
      erw [Pr_bind, Pr_bind, Pr_bind]
      rw [← ENNReal.tsum_add]
      simp_rw [← mul_add]
      -- 1. ゴールの中にある複雑な第1項が、任意の x, target について定理の形と一致することを示す
      have h_sub (x_val : α) (target_val : Bool) :
        Pr (do
          let x ← uniformOfFintype Bool
          let x_1 ← A (x_val, x)
          let b ← PMF.pure (if (x_1 == 1) = true then x else !x)
          PMF.pure (b == target_val)) =
        Pr (do
          let w ← uniformOfFintype Bool
          let a ← (fun w => A (x_val, w)) w
          PMF.pure ((if a == 1 then w else !w) == target_val)) := by
        -- 定義の展開とモナドの法則（pure_bind）だけで一致するはず
        simp only [Fin.isValue, beq_iff_eq]
        congr; funext x; congr; funext x_1;
        simp only [Bind.bind, PMF.pure_bind]

      simp_rw [h_sub]
      simp_rw [Pr_prediction_logic]
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
      rw [ENNReal.tsum_mul_right, tsum_coe,one_mul]


    -- ENNReal の等式 h_enn を toReal して h_real_goal を導く
    -- (ENNReal.toReal_add 等を使用して和を分配する)
    have h_toReal := congrArg ENNReal.toReal h_enn
    -- 確率値が有限であることを保証する補題 (ne_top) を適宜使用
    erw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] at h_toReal
    erw [ENNReal.toReal_add (by norm_num) (PMF.apply_ne_top _ _)] at h_toReal
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h_toReal
    exact h_toReal
  have h_real_goal2 :
      (Pr (do let (x, p_x) ← X_joint; let b ← predictor_B A x; PMF.pure (b == p_x))).toReal
      = (1 / 2 : ℝ) + (Pr (do let (x, p_x) ← X_joint; let a ← A (x, p_x); PMF.pure (a == 1))).toReal - (Pr (do let (x, _) ← X_joint; let b ← PMF.uniformOfFintype Bool; let a ← A (x, b); PMF.pure (a == 1))).toReal := by
    exact eq_sub_of_add_eq h_real_goal
  rw [h_real_goal2]
  rw [add_sub_assoc]
  congr; funext y;
  simp only [bind_assoc]
  rw [← U1_to_bool]
  simp only [Bind.bind]
  simp only [Fin.isValue, PMF.bind_map, zero_lt_one, BitVec.getLsbD_eq_getElem, PMF.pure_bind]
  congr


/-- 補題 4.2: 計算量と成功確率の保証 -/
lemma prediction_lemma {α : Type} (X_joint : PMF (α × Bool))
    (A : α × Bool → PMF Bit) (tA : ℕ) (ε : ℝ) (t_redB : ℕ) :
    |advantage X_joint A| > ε →
    ∃ (B : α → PMF Bool) (tB : ℕ),
      tB = tA + t_redB ∧
      prediction_success_prob X_joint B > 1 / 2 + ε := by

  intro h_abs
  have h_cases := lt_abs.mp h_abs
  cases h_cases with
  | inl h_pos => -- adv > ε
      use (predictor_B A), (tA + t_redB)
      constructor
      · rfl
      · rw [predictor_B_success_eq_half_plus_adv]
        linarith
  | inr h_neg => -- adv < -ε
      use (predictor_B (negate_distinguisher A)), (tA + t_redB)
      -- A を反転させた場合でも計算量の増分 t_redB は同じと仮定（または調整）
      constructor
      · sorry
      · -- Adv(A_not) = -Adv(A) を用いて linarith
        sorry

-- ============================================================
-- 4. 定理 4.2 (NB-予測不可能 ↔ 擬似ランダム)
-- ============================================================

-- ============================================================
-- 1. ビット切り出しと同型写像の定義 (X_joint)
-- ============================================================

/-- 分布 X から (prefix, next_bit) を取り出すジョイント分布。
    bv_split3_i i を使い、真ん中の 1ビットを Bool として取り出す。 -/
noncomputable def X_joint (X : PMF (BitVec L)) (i : Fin L) : PMF (BitVec i × Bool) :=
  X.map (fun x =>
    let triple := bv_split3_i i x
    (triple.1, triple.2.1.getLsbD 0) -- BitVec 1 を Bool に変換
  )

-- ============================================================
-- 2. ハイブリッド分布の定義
-- ============================================================
-- ============================================================
-- 1. `castEquiv` と `bitvecEquiv'` (型問題を解決するインフラ)
-- ============================================================


/-- L = i + (L - i) という証明を内蔵した bitvec_equiv。
    これにより H の定義での型エラーを根本的に解決する。 -/
noncomputable def bitvecEquiv' (L : ℕ) (i : Fin (L + 1)) : BitVec L ≃ BitVec i × BitVec (L - i) := by
  exact @bv_split_i L i

/-- H i : bitvecEquiv' を使うことで、型エラーを回避した定義。 -/
noncomputable def H (X : PMF (BitVec L)) (i : Fin (L + 1)) : PMF (BitVec L) :=
  do
    let x ← X
    let u ← U L
    -- L = i + (L-i) の証明 h を内蔵した bitvecEquiv' で分解・結合
    let x_parts := bitvecEquiv' L i x
    let u_parts := bitvecEquiv' L i u
    PMF.pure ((bitvecEquiv' L i).symm (x_parts.1, u_parts.2))



-- ============================================================
-- 3. ハイブリッド関連の補題 (インフラ層)
-- ============================================================

/-- [境界 0]: H X 0 = U L -/
lemma H_zero_eq_U (X : PMF (BitVec L)) : H X 0 = U L := by
  unfold H
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero]

  calc
    (do let x ← X; let u ← U L
        let x_parts := bitvecEquiv' L 0 x
        let u_parts := bitvecEquiv' L 0 u
        PMF.pure ((bitvecEquiv' L 0).symm (x_parts.1, u_parts.2)))
    -- Step 1: BitVec 0 の唯一性により、x_parts.1 は u_parts.1 と等しい
    _ = (do let x ← X; let u ← U L
            let u_parts := bitvecEquiv' L 0 u
            PMF.pure ((bitvecEquiv' L 0).symm (u_parts.1, u_parts.2))) := by
        congr; funext x; congr; funext u
        -- x_parts.1 と u_parts.1 は共に BitVec 0 なので一致する
        have h_pre : (bitvecEquiv' L 0 x).1 = (bitvecEquiv' L 0 u).1 := by
          exact BitVec.eq_of_getMsbD_eq fun i ↦ congrFun rfl
        simp only [h_pre]
    -- Step 2: (u_parts.1, u_parts.2) は bitvecEquiv' の適用結果そのものなので、symm で u に戻る
    _ = (do let x ← X; let u ← U L; PMF.pure u) := by
        congr; funext x; congr; funext u
        simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    -- Step 3: u を pure して終わる分布は、単なる U L と等しい (bind_pure)
    _ = (do let x ← X; U L) := by
        congr; funext x
        exact PMF.bind_pure (U L)
    -- Step 4: 結果に使われないサンプル x を破棄する (bind_const)
    _ = U L := by
        exact PMF.bind_const X (U L)


/-- [境界 L]: H X L = X -/
lemma H_L_eq_X (X : PMF (BitVec L)) : H X (Fin.last L) = X := by
  unfold H
  -- L ≤ L は自明
  simp only [Fin.val_last]

  calc
    (do let x ← X; let u ← U L
        let x_parts := bitvecEquiv' L (Fin.last L) x
        let u_parts := bitvecEquiv' L (Fin.last L) u
        PMF.pure ((bitvecEquiv' L (Fin.last L)).symm (x_parts.1, u_parts.2)))
    -- Step 1: BitVec 0 (suffix) の唯一性により、u_parts.2 は x_parts.2 と等しい
    _ = (do let x ← X; let u ← U L
            let x_parts := bitvecEquiv' L (Fin.last L) x
            PMF.pure ((bitvecEquiv' L (Fin.last L)).symm (x_parts.1, x_parts.2))) := by
        congr; funext x; congr; funext u
        -- x_parts.2 と u_parts.2 は共に BitVec 0 なので一致する
        have h_suf : (bitvecEquiv' L (Fin.last L) u).2 = (bitvecEquiv' L (Fin.last L) x).2 := by
          simp only [Fin.val_last]
          apply Subsingleton.elim
        -- let 束縛を展開しながら h_suf を適用
        simp only [h_suf]
    -- Step 2: (x_parts.1, x_parts.2) を symm で戻すと x になる (symm_apply_apply)
    _ = (do let x ← X; let u ← U L; PMF.pure x) := by
        congr; funext x; congr; funext u
        simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    -- Step 3: 結果に使われないサンプル u を破棄する (bind_const)
    _ = (do let x ← X; PMF.pure x) := by
        congr; funext x
        exact PMF.bind_const (U L) (PMF.pure x)
    -- Step 4: サンプルした値をそのまま pure するのは、元の分布 X そのもの (bind_pure)
    _ = X := by
        exact PMF.bind_pure X


/-- [中間ステップの架け橋]: H X i と H X (i+1) を、bv_split3_i i を使った形に展開する。
    この補題の内部だけが、本プロジェクトで唯一ビット演算を許容する場所とする。 -/
lemma H_step_equiv_triple (X : PMF (BitVec L)) (i : Fin L) :
    let i_curr : Fin (L + 1) := ⟨i.castSucc, by omega⟩
    let i_next : Fin (L + 1) := ⟨i.succ, by omega⟩
    -- H i は: prefix=X, bit=U, suffix=U
    (H X i_curr = do
      let x ← X; let u_bit ← U 1; let u_suf ← U (L - i - 1)
      let x_pre := (bv_split3_i i x).1
      PMF.pure ((bv_split3_i i).symm (x_pre, u_bit, u_suf))) ∧
    -- H (i+1) は: prefix=X, bit=X, suffix=U
    (H X i_next = do
      let x ← X; let u_suf ← U (L - i - 1)
      let (x_pre, x_bit, _) := bv_split3_i i x
      PMF.pure ((bv_split3_i i).symm (x_pre, x_bit, u_suf))) := by
  -- ここで BitVec.extractLsb' の結合・分解と bitvecEquiv' / bv_split3_i の整合性を示す
  -- (かなり泥臭いビット演算になるが、一度示せば封印できる)
  sorry


/-- [中間ステップのブリッジ]: H i と H i+1 の差分が X_joint のアドバンテージと一致することの保証。
    ★ここが唯一「ビット演算の沼」を背負い、bv_split3_i と H の整合性を証明する場所。 -/
lemma H_step_diff_eq_advantage (X : PMF (BitVec L)) (i : Fin L) (A : BitVec L → PMF Bit) :
    let A_prime := fun (pair : BitVec i × Bool) => do
      let suf ← U (L - i - 1)
      let b_vec := bv_to_bool.symm pair.2
      A ((bv_split3_i i).symm (pair.1, b_vec, suf))
    |PrDX_one (H X i.succ) A - PrDX_one (H X ⟨i, by omega⟩) A| = |advantage (X_joint X i) A_prime| := by
  intro A_prime
  -- 1. ブリッジ補題を用いて H i と H i+1 を展開
  obtain ⟨h_curr, h_next⟩ := H_step_equiv_triple X i

  -- 2. PrDX_one (H X (i+1)) A = PrDX_one (X_joint X i) A_prime を示す
  have h_Pr_next : PrDX_one (H X i.succ) A = PrDX_one (X_joint X i) A_prime := by
    have h_enn : Pr (do let x ← H X i.succ; let a ← A x; PMF.pure (a == 1)) =
               Pr (do let pair ← X_joint X i; let a ← A_prime pair; PMF.pure (a == 1)) := by
      calc
        Pr (do let x ← H X i.succ; let a ← A x; PMF.pure (a == 1))
        -- Step 1: ハイブリッド分布 H(i+1) を 3 分割の定義に展開 (インフラ補題を使用)
        _ = Pr (do
              let x ← X; let u ← U L
              let (x_pre, x_bit, _) := bv_split3_i i x
              let (_, _, u_suf) := bv_split3_i i u
              let a ← A ((bv_split3_i i).symm (x_pre, x_bit, u_suf))
              PMF.pure (a == 1)) := by
                rw [h_next]
                simp only [Equiv.toFun_as_coe, Fin.isValue, bind_assoc]
                congr; funext x;
                rw [U_split3_i i]
                simp only [Fin.isValue, bind_assoc]
                simp only [pure_bind_do]
                simp only [bv_join3_i, Equiv.apply_symm_apply]
                simp only [bind_unused]

        -- Step 2: U L をライブラリの定理 U_split3_i で 3 つの独立なサンプリングに分解
        _ = Pr (do
              let x ← X
              let _u_pre ← U i; let _u_bit ← U 1; let u_suf ← U (L - i - 1)
              let (x_pre, x_bit, _) := bv_split3_i i x
              let a ← A ((bv_split3_i i).symm (x_pre, x_bit, u_suf))
              PMF.pure (a == 1)) := by
            simp_rw [U_split3_i i, bind_assoc, pure_bind_do]
            -- u の prefix と bit は H(i+1) では使われないため、簡約して消える準備をする
            simp only [bv_join3_i]
            simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply, Fin.isValue, bind_unused]
        -- Step 3: 使っていない _u_pre, _u_bit をライブラリの bind_unused で消去
        _ = Pr (do
              let x ← X; let u_suf ← U (L - i - 1)
              let (x_pre, x_bit, _) := bv_split3_i i x
              let a ← A ((bv_split3_i i).symm (x_pre, x_bit, u_suf))
              PMF.pure (a == 1)) := by
            simp only [bind_unused]
        -- Step 4: X からのサンプリングを X_joint (X.map) の形にパッキングする
        _ = Pr (do
              let pair ← X_joint X i
              let a ← A_prime pair
              PMF.pure (a == 1)) := by
            unfold X_joint A_prime
            -- map と bind の交換法則 (bind_map) で X.map を do pair ← X_joint に戻す
            unfold PMF.map
            simp only [bind_bind_do, Function.comp_apply, pure_bind_do, bind_assoc]
            simp only [Equiv.toFun_as_coe, Fin.isValue, zero_lt_one, BitVec.getLsbD_eq_getElem]
            congr 2; funext x; congr 1; funext u_suf; congr 5;
            rw [← bv_to_bool.left_inv ((bv_split3_i i) x).2.1]
            simp only [bv_to_bool]
            simp_all
            split
            · next h => simp_all only [BitVec.getElem_one, decide_true, ↓reduceIte]
            · next h => simp_all only [BitVec.getElem_zero, Bool.false_eq_true, ↓reduceIte]
    unfold PrDX_one
    simp
    exact congrArg ENNReal.toReal h_enn

  -- 3. PrDX_one (H X i) A = PrDX_one (do ... U 1) A_prime を示す
  have h_Pr_curr : PrDX_one (H X i.castSucc) A =
      PrDX_one (do let (pre, _) ← X_joint X i; let u ← U 1; PMF.pure (pre, u.getLsbD 0)) A_prime := by
    have h_enn : Pr (do let x ← H X i.castSucc; let a ← A x; PMF.pure (a == 1)) =
               Pr (do let pair ← X_joint X i; let u ← U 1; let a ← A_prime (pair.1, u.getLsbD 0); PMF.pure (a == 1)) := by
      calc
        Pr (do let x ← H X i.castSucc; let a ← A x; PMF.pure (a == 1))
        -- 1. H(i) を 3分割形式の定義に展開 (h_curr を使用)
        -- prefix は X から、bit と suffix は U L から取る形
        _ = Pr (do
              let x ← X; let u ← U L
              let x_pre := (bv_split3_i i x).1
              let (_, u_bit, u_suf) := bv_split3_i i u
              let a ← A ((bv_split3_i i).symm (x_pre, u_bit, u_suf))
              PMF.pure (a == 1)) := by
                simp only [h_curr, bind_assoc]
                congr 2; funext x
                simp only [U_split3_i i, bind_assoc, pure_bind_do]
                simp only [Equiv.toFun_as_coe, Prod.mk.eta]
                simp only [bv_join3_i, Equiv.apply_symm_apply]
                simp only [bind_unused]
        -- 2. U L を U_split3_i でバラす (★ライブラリの真骨頂)
        _ = Pr (do
              let x ← X
              let _u_pre ← U i; let u_bit ← U 1; let u_suf ← U (L - i - 1)
              let x_pre := (bv_split3_i i x).1
              let a ← A ((bv_split3_i i).symm (x_pre, u_bit, u_suf))
              PMF.pure (a == 1)) := by
                simp_rw [U_split3_i i, bind_assoc, pure_bind_do,Prod.mk.eta]
                simp only [Equiv.toFun_as_coe]
                simp only [bv_join3_i, Equiv.apply_symm_apply]
        -- 3. 未使用サンプリング (_u_pre) を削除
        _ = Pr (do
              let x ← X; let u_bit ← U 1; let u_suf ← U (L - i - 1)
              let x_pre := (bv_split3_i i x).1
              let a ← A ((bv_split3_i i).symm (x_pre, u_bit, u_suf))
              PMF.pure (a == 1)) := by
            simp only [bind_unused]

        -- 4. X のサンプリングを X_joint にパッケージし、u_bit を使って A_prime に繋ぐ
        _ = Pr (do
              let pair ← X_joint X i
              let u ← U 1
              let a ← A_prime (pair.1, u.getLsbD 0)
              PMF.pure (a == 1)) := by
            unfold X_joint A_prime
            simp only [bind_assoc]
            simp [Bind.bind]; congr; funext pair; congr; funext u_bit; congr; funext u_suf
            congr;
            exact (Equiv.symm_apply_eq bv_to_bool.symm).mp rfl
    unfold PrDX_one
    apply congrArg ENNReal.toReal
    simp only [bind_assoc]
    simp only [h_enn]
    simp only [pure_bind_do]


  -- 4. advantage の定義に代入
  unfold advantage
  rw [h_Pr_next]
  erw [h_Pr_curr]


-- ============================================================
-- 4. 定理 4.2 本体 (メインロジック)
-- ============================================================

/-- 定理 4.2: 擬似ランダムでない ⇒ NB予測可能 (対偶)
    t_redH: ハイブリッド識別器 A' を作る際のオーバーヘッド
    t_redB: 予測器 B を作る際のオーバーヘッド (補題4.2の分) -/
theorem unpredictability_implies_pseudorandomness {L : ℕ} {X : PMF (BitVec L)}
    (t : ℕ) (ε : NNReal) (t_redH t_redB : ℕ) (hL : L > 0) :
    -- 仮定: 計算量 (t + t_redH + t_redB) 内で、アドバンテージ ε * L で識別できる敵がいる
    ¬ DistIndistinguishable X (U L) (t + t_redH + t_redB) (ε * L) →
    -- 結論: 計算量 t 内で、アドバンテージ ε/2 で予測できる予測器が存在する
    -- (※ NextBitUnpredictable の定義内の ε は ℝ 上の ε/2 として扱われる)
    ¬ NextBitUnpredictable X t ε := by
  -- A. 準備: 識別器 A を取り出す
  intro h_not_pr
  unfold DistIndistinguishable at h_not_pr
  push_neg at h_not_pr
  obtain ⟨A, tA, htA, h_adv_A⟩ := h_not_pr

  -- B. ハイブリッド境界 i の特定
  have h_total_adv : |PrDX_one (H X 0) A - PrDX_one (H X (Fin.last L)) A| > ((ε * L : NNReal) : ℝ) := by
    rw [abs_sub_comm] -- |a - b| = |b - a| を使って順序を入れ替え
    rw [H_L_eq_X, H_zero_eq_U]
    -- ここで h_adv_A と一致するはずです。
    -- もし型の詳細で詰まる場合は、一度 (h_adv_A : |PrDX_one X A - PrDX_one (U L) A| > (ε * L : ℝ))
    -- との整合性を確認してください。
    exact h_adv_A

  -- 既存の hybrid_lemma を適用して i を得る。
  -- H は型制限が厳しいのでNatを渡るようにラッパーを作る。
  let H_nat := fun (i : ℕ) => H X (if h : i < L + 1 then ⟨i, h⟩ else Fin.last L)
  have h_nat_0 : H_nat 0 = H X 0 := by
    dsimp [H_nat]
  have h_nat_L : H_nat L = H X (Fin.last L) := by
    dsimp [H_nat]
    simp only [Nat.lt_succ_self, ↓reduceDIte]
    -- Fin L+1 の値 L は Fin.last L と定義上一致する
    rfl
  have h_total_adv_nat : |PrDX_one (H_nat 0) A - PrDX_one (H_nat L) A| > ((ε * L : NNReal) : ℝ) := by
    rw [h_nat_0, h_nat_L]
    exact h_total_adv

  have h_exists_i := hybrid_lemma H_nat L (t + t_redH + t_redB) (ε * L) hL A h_total_adv_nat
  -- have h_exists_i := hybrid_lemma (H X) L (t + t_redH + t_redB) (ε * L) hL A h_total_adv
  obtain ⟨i, hi_range, h_adv_step⟩ := h_exists_i
  let i_fin : Fin L := ⟨i, hi_range⟩

  -- C. 1ビット識別器 A' の構成 (bv_split3_i.symm を使用)
  -- A' の引数は (BitVec i × BitVec 1)
  let A_prime := fun (pair : BitVec i_fin × Bool) => do
    let suf ← U (L - i - 1)
    -- boolEquiv (ProbabilityUtils.leanで定義) を使って Bool を BitVec 1 に変換
    -- これによりビット演算 (if b then 1#1 else 0#1) を回避しつつ同型を維持する
    let b_vec := bv_to_bool.symm pair.2
    A ((bv_split3_i i_fin).symm (pair.1, b_vec, suf))

  -- D. A' のアドバンテージ評価
  -- H_step_diff_eq_advantage により、境界の差分を A' の Advantage に変換
  have h_adv_A' : |advantage (X_joint X i_fin) A_prime| > (ε : ℝ) := by
    -- advantage の定義と H_step_diff_eq_advantage の整合性を利用
    -- (※ X_joint が BitVec 1 ではなく Bool を返す場合は、適宜変換を挟む)
    rw [← H_step_diff_eq_advantage X i_fin A]
    have h_adv_simp : |PrDX_one (H_nat i) A - PrDX_one (H_nat (i + 1)) A| > (ε : ℝ) := by
      norm_cast at h_adv_step
      have : (ε * ↑L / ↑L).toReal = ↑ε := by
        congr
        refine mul_div_cancel_right₀ ε ?_
        aesop
      rw [this] at h_adv_step
      exact h_adv_step

    have h_nat_curr : H_nat i = H X i_fin.castSucc := by
      dsimp [H_nat]
      have h_cond : i < L + 1 := by omega
      rw [dif_pos h_cond]
      rfl
    have h_nat_next : H_nat (i + 1) = H X i_fin.succ := by
      dsimp [H_nat]
      have h_cond : i + 1 < L + 1 := by omega
      rw [dif_pos h_cond]
      rfl
    rw [h_nat_curr, h_nat_next] at h_adv_simp
    rw [abs_sub_comm]
    exact h_adv_simp


  -- E. 予測補題 (Lemma 4.2) の適用
  -- A' (計算量 tA') から、成功確率が高い予測器 B を得る
  -- ここで A' の計算量 tA' = tA + t_redH と仮定する
  let tA' := tA - t_redB -- 実際には構成に合わせて tA との関係を記述

  -- ε/2 のアドバンテージを得るために A' のアドバンテージ ε を利用
  obtain ⟨B, tB, htB, h_succ_B⟩ := prediction_lemma
                (X_joint X i_fin) A_prime tA' (ε / 2) t_redB (by
                    have : ε.toReal ≥ ε.toReal / 2 := by exact NNReal.half_le_self ε
                    linarith [this, h_adv_A'])

  -- F. 結論の構築
  unfold NextBitUnpredictable
  push_neg
  -- i_fin 番目のビットに対する予測器 B を提示
  use i_fin, B, tB
  constructor
  · -- 計算量制約 tB ≤ t を示す
    -- tA ≤ t + t_redH + t_redB かつ tB = tA' + t_redB などの関係を用いる
    sorry
  · -- 成功確率の評価
    -- prediction_success_prob の定義が Pr_predict_success と一致することを示す
    -- h_succ_B : 成功確率 > 1/2 + ε/2
    sorry

end ComputationalSecurity
