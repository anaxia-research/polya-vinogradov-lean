import Mathlib

/-!
# The Pólya–Vinogradov inequality

For a primitive Dirichlet character `χ` modulo `N > 1` and all `M L : ℕ`,
`‖∑_{i < L} χ (M + i)‖ ≤ √N * (1 + log N)`.

Proof: Fourier-expand `χ` using its Gauss sum `τ` (`‖τ‖ = √N`), interchange sums,
bound each geometric sum by `(N/2)(1/a + 1/(N-a))` via Jordan's inequality, and sum
these to `N * H_{N-1} ≤ N (1 + log N)`.
-/

open ZMod DirichletCharacter Finset Complex

namespace PolyaVinogradov

variable {N : ℕ} [NeZero N]

/-! ### Step 1: `‖τ(χ)‖ = √N` -/

lemma dft_star (Φ : ZMod N → ℂ) (k : ZMod N) :
    𝓕 (fun j ↦ (starRingEnd ℂ) (Φ j)) k = (starRingEnd ℂ) (𝓕 Φ (-k)) := by
  simp only [dft_apply, smul_eq_mul, map_sum, map_mul]
  refine sum_congr rfl fun j _ ↦ ?_
  congr 1
  rw [← AddChar.map_neg_eq_conj]
  congr 1
  ring

omit [NeZero N] in
lemma inv_apply_eq_conj (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    χ⁻¹ a = (starRingEnd ℂ) (χ a) := by
  rw [← MulChar.star_apply' χ a]; rfl

theorem normSq_gaussSum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ stdAddChar‖ ^ 2 = N := by
  set τ := gaussSum χ stdAddChar with hτ
  have hF : ∀ k, 𝓕 χ k = χ⁻¹ (-k) * τ := fun k ↦ hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hinv := inv_apply_eq_conj χ
  have h1 : ∀ j, 𝓕 (𝓕 χ) j = (N : ℂ) * χ (-j) := fun j ↦ by
    rw [dft_dft]; simp [smul_eq_mul]
  have h2 : ∀ j, 𝓕 (𝓕 χ) j = (starRingEnd ℂ) τ * τ * χ (-j) := fun j ↦ by
    have e1 : (𝓕 χ) = fun k ↦ (fun k ↦ (starRingEnd ℂ) (χ (-k))) k * τ := by
      funext k; rw [hF, hinv]
    rw [e1, dft_mul_const]
    have e2 : 𝓕 (fun k ↦ (starRingEnd ℂ) (χ (-k))) j
        = (starRingEnd ℂ) (𝓕 (fun k ↦ χ (-k)) (-j)) := dft_star (fun k ↦ χ (-k)) j
    dsimp only
    rw [e2, dft_comp_neg]
    simp only [neg_neg]
    rw [hF, hinv, map_mul, starRingEnd_self_apply]
    ring
  have key := (h1 (-1)).symm.trans (h2 (-1))
  simp only [neg_neg, map_one, mul_one] at key
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at key
  exact_mod_cast key.symm

theorem norm_gaussSum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ stdAddChar‖ = Real.sqrt N := by
  rw [← normSq_gaussSum hχ, Real.sqrt_sq (norm_nonneg _)]

/-! ### Step 2: Fourier expansion of `χ` -/

lemma fourier_expansion {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (x : ZMod N) :
    χ x = (N : ℂ)⁻¹ * gaussSum χ stdAddChar *
      ∑ k : ZMod N, χ⁻¹ (-k) * stdAddChar (k * x) := by
  have h := congrFun (LinearEquiv.symm_apply_apply (dft (E := ℂ) (N := N)) χ) x
  rw [← h, invDFT_apply]
  simp only [hχ.fourierTransform_eq_inv_mul_gaussSum, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  ring

/-! ### Step 3: the geometric sum bound -/

/-- Jordan-type bound: `sin (π t) ≥ 2 t (1 - t)` for `t ∈ [0,1]`. -/
lemma two_mul_mul_le_sin {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    2 * t * (1 - t) ≤ Real.sin (Real.pi * t) := by
  rcases le_total t (1 / 2) with ht | ht
  · have := Real.mul_le_sin (x := Real.pi * t) (by positivity) (by nlinarith [Real.pi_pos])
    have e : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    nlinarith
  · have hs : Real.sin (Real.pi * t) = Real.sin (Real.pi * (1 - t)) := by
      rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.sin_pi_sub]
    have := Real.mul_le_sin (x := Real.pi * (1 - t)) (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
    have e : 2 / Real.pi * (Real.pi * (1 - t)) = 2 * (1 - t) := by field_simp
    nlinarith

lemma stdAddChar_eq_exp (k : ZMod N) :
    (stdAddChar k : ℂ) = Complex.exp (I * ((2 * Real.pi * k.val / N : ℝ) : ℂ)) := by
  rw [stdAddChar_apply, toCircle_apply]
  congr 1
  push_cast
  ring

lemma norm_stdAddChar (k : ZMod N) : ‖(stdAddChar k : ℂ)‖ = 1 := by
  rw [stdAddChar_apply]; exact Circle.norm_coe _

/-- For `k ≠ 0`, `‖∑_{i<L} e(k)^i‖ ≤ (N/2)(1/k.val + 1/(N - k.val))`. -/
lemma norm_geom_sum_le (k : ZMod N) (hk : k ≠ 0) (L : ℕ) :
    ‖∑ i ∈ range L, (stdAddChar k : ℂ) ^ i‖ ≤
      (N / 2 : ℝ) * (1 / (k.val : ℝ) + 1 / ((N : ℝ) - k.val)) := by
  set v : ℝ := (k.val : ℝ) with hv
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hv0 : 0 < v := by
    have : k.val ≠ 0 := (ZMod.val_ne_zero k).mpr hk
    rw [hv]; exact_mod_cast Nat.pos_of_ne_zero this
  have hvN : v < N := by rw [hv]; exact_mod_cast ZMod.val_lt k
  set t : ℝ := v / N with ht
  have ht0 : 0 < t := div_pos hv0 hNpos
  have ht1 : t < 1 := (div_lt_one hNpos).mpr hvN
  set z : ℂ := stdAddChar k with hz
  -- `‖z - 1‖ = 2 sin(π t)`
  have hz1 : ‖z - 1‖ = 2 * Real.sin (Real.pi * t) := by
    rw [hz, stdAddChar_eq_exp, Complex.norm_exp_I_mul_ofReal_sub_one]
    have e : 2 * Real.pi * (k.val : ℝ) / N / 2 = Real.pi * t := by
      rw [ht, hv]; ring
    rw [e, Real.norm_eq_abs, abs_of_nonneg]
    have := two_mul_mul_le_sin ht0.le ht1.le
    nlinarith
  have hsin := two_mul_mul_le_sin ht0.le ht1.le
  have hpos : 0 < 2 * t * (1 - t) := by nlinarith
  have hz1pos : 0 < ‖z - 1‖ := by rw [hz1]; nlinarith
  -- geometric sum identity
  have hg : (∑ i ∈ range L, z ^ i) * (z - 1) = z ^ L - 1 := geom_sum_mul z L
  have hnum : ‖z ^ L - 1‖ ≤ 2 := by
    calc ‖z ^ L - 1‖ ≤ ‖z ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, norm_stdAddChar, one_pow, norm_one]; norm_num
  have hS : ‖∑ i ∈ range L, z ^ i‖ ≤ 2 / ‖z - 1‖ := by
    rw [le_div_iff₀ hz1pos, ← norm_mul, hg]; exact hnum
  calc ‖∑ i ∈ range L, z ^ i‖ ≤ 2 / ‖z - 1‖ := hS
    _ ≤ 2 / (4 * t * (1 - t)) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by nlinarith)
        rw [hz1]; nlinarith
    _ = (N / 2 : ℝ) * (1 / v + 1 / ((N : ℝ) - v)) := by
        rw [ht]
        have h1 : (N : ℝ) - v ≠ 0 := by linarith
        field_simp
        ring

/-! ### Step 4: summing the bounds -/

lemma sum_inv_val_le :
    ∑ k ∈ univ.filter (fun k : ZMod N ↦ k ≠ 0), (1 / (k.val : ℝ)) ≤ 1 + Real.log N := by
  classical
  have hinj : Set.InjOn (fun k : ZMod N ↦ k.val) ↑(univ.filter fun k : ZMod N ↦ k ≠ 0) :=
    fun a _ b _ h ↦ ZMod.val_injective N h
  rw [← sum_image (f := fun a : ℕ ↦ 1 / (a : ℝ)) hinj]
  have hsub : (univ.filter fun k : ZMod N ↦ k ≠ 0).image (fun k ↦ k.val) ⊆ Ico 1 N := by
    intro a ha
    simp only [mem_image, mem_filter, mem_univ, true_and] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    simp only [mem_Ico]
    exact ⟨Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero k).mpr hk), ZMod.val_lt k⟩
  calc _ ≤ ∑ a ∈ Ico 1 N, 1 / (a : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
    _ = (harmonic (N - 1) : ℝ) := by
        rw [sum_Ico_eq_sum_range, harmonic]
        push_cast
        refine sum_congr rfl fun i _ ↦ ?_
        rw [add_comm]; simp
    _ ≤ 1 + Real.log (N - 1 : ℕ) := harmonic_le_one_add_log _
    _ ≤ 1 + Real.log N := by
        have : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log N := by
          rcases Nat.eq_zero_or_pos (N - 1) with h | h
          · rw [h, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg N
          · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.sub_le N 1)
        linarith

lemma sum_inv_neg_val_eq :
    ∑ k ∈ univ.filter (fun k : ZMod N ↦ k ≠ 0), (1 / ((N : ℝ) - k.val)) =
      ∑ k ∈ univ.filter (fun k : ZMod N ↦ k ≠ 0), (1 / (k.val : ℝ)) := by
  refine sum_nbij' (fun k ↦ -k) (fun k ↦ -k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simpa using hk
  · intro k hk; simpa using hk
  · intro k _; simp
  · intro k _; simp
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    have : NeZero k := ⟨hk⟩
    rw [ZMod.val_neg_of_ne_zero, Nat.cast_sub (ZMod.val_lt k).le]

/-! ### Step 5: the Pólya–Vinogradov inequality -/

lemma geom_rewrite (k : ZMod N) (M L : ℕ) :
    ∑ i ∈ range L, (stdAddChar (k * ((M + i : ℕ) : ZMod N)) : ℂ) =
      stdAddChar (k * (M : ZMod N)) * ∑ i ∈ range L, (stdAddChar k : ℂ) ^ i := by
  rw [mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Nat.cast_add, mul_add, AddChar.map_add_eq_mul, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
    mul_comm (i : ZMod N) k]

/-- **Pólya–Vinogradov inequality.** For a primitive Dirichlet character `χ` modulo `N > 1`,
every sum of `χ` over an interval of consecutive integers is at most `√N (1 + log N)`. -/
theorem polya_vinogradov {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (M L : ℕ) :
    ‖∑ i ∈ range L, χ ((M + i : ℕ) : ZMod N)‖ ≤ Real.sqrt N * (1 + Real.log N) := by
  classical
  have : Fact (1 < N) := ⟨hN⟩
  set τ := gaussSum χ stdAddChar with hτ
  set F := univ.filter (fun k : ZMod N ↦ k ≠ 0) with hF
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_one.trans hN)
  -- expand and interchange
  have hS : ∑ i ∈ range L, χ ((M + i : ℕ) : ZMod N) =
      (N : ℂ)⁻¹ * τ * ∑ k : ZMod N, χ⁻¹ (-k) *
        ∑ i ∈ range L, (stdAddChar (k * ((M + i : ℕ) : ZMod N)) : ℂ) := by
    simp_rw [fourier_expansion hχ, ← mul_sum]
    rw [sum_comm, ← hτ]
    simp_rw [mul_sum]
  -- termwise bound
  set b : ZMod N → ℝ := fun k ↦
    if k = 0 then 0 else (N / 2 : ℝ) * (1 / (k.val : ℝ) + 1 / ((N : ℝ) - k.val)) with hb
  have hterm : ∀ k : ZMod N, ‖χ⁻¹ (-k) *
      ∑ i ∈ range L, (stdAddChar (k * ((M + i : ℕ) : ZMod N)) : ℂ)‖ ≤ b k := by
    intro k
    by_cases hk : k = 0
    · simp [hk, hb, MulChar.map_zero]
    · simp only [hb, hk, if_false]
      rw [geom_rewrite, norm_mul, norm_mul, norm_stdAddChar, one_mul]
      calc ‖χ⁻¹ (-k)‖ * ‖∑ i ∈ range L, (stdAddChar k : ℂ) ^ i‖
          ≤ 1 * ‖∑ i ∈ range L, (stdAddChar k : ℂ) ^ i‖ := by
            gcongr; exact DirichletCharacter.norm_le_one χ⁻¹ (-k)
        _ ≤ _ := by rw [one_mul]; exact norm_geom_sum_le k hk L
  have hsumb : ∑ k : ZMod N, b k ≤ (N : ℝ) * (1 + Real.log N) := by
    have : ∑ k : ZMod N, b k = (N / 2 : ℝ) *
        (∑ k ∈ F, 1 / (k.val : ℝ) + ∑ k ∈ F, 1 / ((N : ℝ) - k.val)) := by
      simp only [hF, sum_filter, ← sum_add_distrib, mul_sum]
      refine sum_congr rfl fun k _ ↦ ?_
      by_cases hk : k = 0 <;> simp [hb, hk]
    rw [this, hF, sum_inv_neg_val_eq]
    have h := sum_inv_val_le (N := N)
    nlinarith
  calc ‖∑ i ∈ range L, χ ((M + i : ℕ) : ZMod N)‖
      = (N : ℝ)⁻¹ * Real.sqrt N * ‖∑ k : ZMod N, χ⁻¹ (-k) *
          ∑ i ∈ range L, (stdAddChar (k * ((M + i : ℕ) : ZMod N)) : ℂ)‖ := by
        rw [hS, norm_mul, norm_mul, hτ, norm_gaussSum hχ, norm_inv, Complex.norm_natCast]
    _ ≤ (N : ℝ)⁻¹ * Real.sqrt N * ∑ k : ZMod N, b k := by
        gcongr
        exact (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ hterm k)
    _ ≤ (N : ℝ)⁻¹ * Real.sqrt N * ((N : ℝ) * (1 + Real.log N)) := by gcongr
    _ = Real.sqrt N * (1 + Real.log N) := by field_simp

end PolyaVinogradov

#print axioms PolyaVinogradov.polya_vinogradov
