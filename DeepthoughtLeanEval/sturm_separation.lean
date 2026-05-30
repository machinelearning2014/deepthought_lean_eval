import Mathlib
open Set
open Real
open MeasureTheory
open Filter

open scoped Topology

noncomputable section

lemma uIcc_subset_of_ordConnected (J : Set ℝ) (hJ_conn : IsPreconnected J) (a x : ℝ) (haJ : a ∈ J) (hxJ : x ∈ J) :
    Set.uIcc a x ⊆ J := by
  have h_ord : J.OrdConnected := by
    rwa [isPreconnected_iff_ordConnected] at hJ_conn
  intro y hy
  rw [Set.mem_uIcc] at hy
  rcases hy with (⟨hay, hyx⟩ | ⟨hxy, hya⟩)
  · have : y ∈ Set.Icc a x := ⟨hay, hyx⟩
    exact h_ord.out haJ hxJ this
  · have : y ∈ Set.Icc x a := ⟨hxy, hya⟩
    exact h_ord.out hxJ haJ this

lemma integral_hasDerivAt_right_contOn_open (p : ℝ → ℝ) (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp : ContinuousOn p J) (a x : ℝ) (haJ : a ∈ J) (hxJ : x ∈ J) :
    HasDerivAt (fun u : ℝ => ∫ t in a..u, p t) (p x) x := by
  have h_uIcc_sub : Set.uIcc a x ⊆ J := uIcc_subset_of_ordConnected J hJ_conn a x haJ hxJ
  have hp_uIcc : ContinuousOn p (Set.uIcc a x) := hp.mono h_uIcc_sub
  have h_int : IntervalIntegrable p MeasureTheory.volume a x :=
    hp_uIcc.intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter p (nhds x) MeasureTheory.volume := by
    have h_all : ∀ y ∈ J, ContinuousAt p y := by
      intro y hy
      have hcw : ContinuousWithinAt p J y := hp y hy
      have hJ_nhds : J ∈ nhds y := hJ_open.mem_nhds hy
      exact hcw.continuousAt hJ_nhds
    exact ContinuousAt.stronglyMeasurableAtFilter hJ_open h_all x hxJ
  have hb : ContinuousAt p x := by
    have h_all : ∀ y ∈ J, ContinuousAt p y := by
      intro y hy
      have hcw : ContinuousWithinAt p J y := hp y hy
      have hJ_nhds : J ∈ nhds y := hJ_open.mem_nhds hy
      exact hcw.continuousAt hJ_nhds
    exact h_all x hxJ
  exact intervalIntegral.integral_hasDerivAt_right h_int hmeas hb

def W (y₁ y₂ : ℝ → ℝ) (x : ℝ) : ℝ := y₁ x * deriv y₂ x - y₂ x * deriv y₁ x

lemma wronskian_deriv (p q y₁ y₂ : ℝ → ℝ) (x : ℝ)
    (hy₁ : HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x) :
    HasDerivAt (W y₁ y₂) (-(p x * W y₁ y₂ x)) x := by
  unfold W
  have h1 : HasDerivAt (fun t => y₁ t * deriv y₂ t)
      ((deriv y₁ x) * (deriv y₂ x) + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) x :=
    HasDerivAt.mul hy₁ hy₂'
  have h2 : HasDerivAt (fun t => y₂ t * deriv y₁ t)
      ((deriv y₂ x) * (deriv y₁ x) + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x))) x :=
    HasDerivAt.mul hy₂ hy₁'
  have hsub : HasDerivAt (fun t => y₁ t * deriv y₂ t - y₂ t * deriv y₁ t)
      (((deriv y₁ x) * (deriv y₂ x) + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) -
       ((deriv y₂ x) * (deriv y₁ x) + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x)))) x :=
    HasDerivAt.sub h1 h2
  have hsimpl : ((deriv y₁ x) * (deriv y₂ x) + y₁ x * (-(p x * deriv y₂ x + q x * y₂ x))) -
      ((deriv y₂ x) * (deriv y₁ x) + y₂ x * (-(p x * deriv y₁ x + q x * y₁ x))) =
      (-(p x * (y₁ x * deriv y₂ x - y₂ x * deriv y₁ x))) := by
    ring
  rw [hsimpl] at hsub
  exact hsub

lemma wronskian_zero_of_point (p q y₁ y₂ : ℝ → ℝ) (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (c : ℝ) (hcJ : c ∈ J) (hWc : W y₁ y₂ c = 0) : ∀ x ∈ J, W y₁ y₂ x = 0 := by
  intro x hxJ
  set I := fun t : ℝ => ∫ s in c..t, p s with hI
  set F := fun t : ℝ => W y₁ y₂ t * Real.exp (I t) with hF
  have hFderiv : ∀ t ∈ J, HasDerivAt F 0 t := by
    intro t htJ
    have hWderiv : HasDerivAt (W y₁ y₂) (-(p t * W y₁ y₂ t)) t :=
      wronskian_deriv p q y₁ y₂ t (hy₁ t htJ) (hy₁' t htJ) (hy₂ t htJ) (hy₂' t htJ)
    have hIderiv : HasDerivAt I (p t) t :=
      integral_hasDerivAt_right_contOn_open p J hJ_open hJ_conn hp c t hcJ htJ
    have hexpderiv : HasDerivAt (Real.exp ∘ I) (Real.exp (I t) * p t) t := by
      have := HasDerivAt.exp hIderiv
      simpa [mul_comm] using this
    have hFderiv' : HasDerivAt F (-(p t * W y₁ y₂ t) * Real.exp (I t) + W y₁ y₂ t * (Real.exp (I t) * p t)) t :=
      HasDerivAt.mul hWderiv hexpderiv
    have : -(p t * W y₁ y₂ t) * Real.exp (I t) + W y₁ y₂ t * (Real.exp (I t) * p t) = 0 := by
      ring
    rw [this] at hFderiv'
    exact hFderiv'
  have hFconst : ∀ x ∈ J, F x = F c := by
    intro x hxJ
    have h_deriv : ∀ t ∈ Set.uIcc c x, HasDerivAt F 0 t := by
      intro t ht
      have htJ : t ∈ J := uIcc_subset_of_ordConnected J hJ_conn c x hcJ hxJ ht
      exact hFderiv t htJ
    have h_int : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume c x :=
      intervalIntegrable_const
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int
    have : (∫ _ : ℝ in c..x, (0 : ℝ)) = 0 := by simp
    rw [this] at hFTC
    linarith
  have hFc : F c = 0 := by
    dsimp [F, I]
    simp [hWc]
  have hFx_eq : F x = 0 := by
    rw [hFconst x hxJ, hFc]
  dsimp [F] at hFx_eq
  have h_exp_pos : 0 < Real.exp (I x) := Real.exp_pos (I x)
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hFx_eq with (h | h)
  · exact h
  · exfalso; linarith

lemma constant_sign_nonzero_cont (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf_nonzero : ∀ x ∈ Set.Ioo a b, f x ≠ 0)
    (hf_cont : ∀ x ∈ Set.Ioo a b, ContinuousAt f x) :
    (∀ x ∈ Set.Ioo a b, f x > 0) ∨ (∀ x ∈ Set.Ioo a b, f x < 0) := by
  by_cases hpos : ∃ x ∈ Set.Ioo a b, f x > 0
  · left
    intro x hx
    by_contra! hx_notpos
    have hx_nonpos : f x ≤ 0 := hx_notpos
    rcases hpos with ⟨x₀, hx₀, hx₀_pos⟩
    by_cases hx_lt_x₀ : x < x₀
    · have hx_le_x₀ : x ≤ x₀ := by linarith
      have h_cont_xx₀ : ContinuousOn f (Set.Icc x x₀) := by
        intro z hz
        rcases hz with ⟨hz1, hz2⟩
        have hz_ioo : z ∈ Set.Ioo a b := by
          rcases hx with ⟨hxa, hxb⟩
          rcases hx₀ with ⟨hx₀a, hx₀b⟩
          refine ⟨by linarith, by linarith⟩
        exact (hf_cont z hz_ioo).continuousWithinAt
      have hzero_in : 0 ∈ Set.Icc (f x) (f x₀) := ⟨hx_nonpos, le_of_lt hx₀_pos⟩
      have h_IVT : 0 ∈ f '' Set.Icc x x₀ :=
        intermediate_value_Icc hx_le_x₀ h_cont_xx₀ hzero_in
      rcases h_IVT with ⟨c, hc, hc_eq⟩
      rcases hc with ⟨hc1, hc2⟩
      have hc_ioo : c ∈ Set.Ioo a b := by
        rcases hx with ⟨hxa, hxb⟩
        rcases hx₀ with ⟨hx₀a, hx₀b⟩
        refine ⟨by linarith, by linarith⟩
      exact hf_nonzero c hc_ioo hc_eq
    · have hx₀_le_x : x₀ ≤ x := by linarith
      have h_cont_x₀x : ContinuousOn f (Set.Icc x₀ x) := by
        intro z hz
        rcases hz with ⟨hz1, hz2⟩
        have hz_ioo : z ∈ Set.Ioo a b := by
          rcases hx with ⟨hxa, hxb⟩
          rcases hx₀ with ⟨hx₀a, hx₀b⟩
          refine ⟨by linarith, by linarith⟩
        exact (hf_cont z hz_ioo).continuousWithinAt
      have hzero_in : 0 ∈ Set.Icc (f x) (f x₀) := ⟨hx_nonpos, le_of_lt hx₀_pos⟩
      have h_IVT : 0 ∈ f '' Set.Icc x₀ x :=
        intermediate_value_Icc' hx₀_le_x h_cont_x₀x hzero_in
      rcases h_IVT with ⟨c, hc, hc_eq⟩
      rcases hc with ⟨hc1, hc2⟩
      have hc_ioo : c ∈ Set.Ioo a b := by
        rcases hx with ⟨hxa, hxb⟩
        rcases hx₀ with ⟨hx₀a, hx₀b⟩
        refine ⟨by linarith, by linarith⟩
      exact hf_nonzero c hc_ioo hc_eq
  · right
    intro x hx
    by_contra! hx_nonneg
    have hx_pos : f x > 0 := by
      by_contra! hx_notpos
      have : f x = 0 := by linarith
      exact hf_nonzero x hx this
    exact hpos ⟨x, hx, hx_pos⟩

lemma deriv_nonneg_of_pos_on_interval (f : ℝ → ℝ) {a r : ℝ} (hr : r > 0)
    (hf_pos : ∀ x ∈ Set.Ioo a (a + r), f x > 0) (hf0 : f a = 0)
    (hderiv : HasDerivAt f (deriv f a) a) : 0 ≤ deriv f a := by
  have h_slope_pos : ∀ x ∈ Set.Ioo a (a + r), 0 < slope f a x := by
    intro x hx
    dsimp [slope]
    simp [hf0]
    have : f x > 0 := hf_pos x hx
    have : x - a > 0 := sub_pos.mpr hx.1
    positivity
  have h_tendsto : Tendsto (slope f a) (𝓝[>] a) (𝓝 (deriv f a)) :=
    hderiv.tendsto_slope.mono_left (nhdsWithin_mono a (fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_gt hx)))
  have h_open_set : Set.Ioo a (a + r) ∈ 𝓝[>] a :=
    Ioo_mem_nhdsGT (by nlinarith : a < a + r)
  have h_slope_nonneg : ∀ᶠ x in 𝓝[>] a, 0 ≤ slope f a x := by
    refine Filter.eventually_of_mem h_open_set ?_
    intro x hx
    exact le_of_lt (h_slope_pos x hx)
  exact ge_of_tendsto h_tendsto h_slope_nonneg

lemma deriv_nonpos_of_pos_on_interval (f : ℝ → ℝ) {b r : ℝ} (hr : r > 0)
    (hf_pos : ∀ x ∈ Set.Ioo (b - r) b, f x > 0) (hf0 : f b = 0)
    (hderiv : HasDerivAt f (deriv f b) b) : deriv f b ≤ 0 := by
  set g := fun t : ℝ => f (b - t) with hg
  have hg_pos : ∀ t ∈ Set.Ioo 0 (0 + r), g t > 0 := by
    intro t ht
    rcases ht with ⟨ht1, ht2⟩
    dsimp [g]
    have : b - t ∈ Set.Ioo (b - r) b := by
      refine ⟨by nlinarith, by nlinarith⟩
    exact hf_pos (b - t) this
  have hg0 : g 0 = 0 := by
    dsimp [g]
    simp [hf0]
  have hg_deriv : HasDerivAt g (-deriv f b) 0 := by
    have h_comp : HasDerivAt (fun t : ℝ => b - t) (-1) 0 := by
      have h_id : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id (0 : ℝ)
      exact HasDerivAt.const_sub b h_id
    have hderiv' : HasDerivAt f (deriv f b) ((fun t : ℝ => b - t) 0) := by
      simpa using hderiv
    have := HasDerivAt.comp (0 : ℝ) hderiv' h_comp
    simpa [g, mul_comm] using this
  have h_nonneg : 0 ≤ deriv g 0 :=
    deriv_nonneg_of_pos_on_interval g hr hg_pos hg0 (by
      rw [hg_deriv.deriv]
      exact hg_deriv)
  have : deriv g 0 = -deriv f b := hg_deriv.deriv
  rw [this] at h_nonneg
  linarith

lemma pos_at_endpoint (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf_pos : ∀ x ∈ Set.Ioo a b, f x > 0) (hf_cont : ContinuousOn f (Set.Icc a b)) (hf_nonzero : f a ≠ 0) : f a > 0 := by
  by_contra! h
  have h_neg : f a < 0 := by
    by_contra! h_nonneg
    have : f a = 0 := by linarith
    exact hf_nonzero this
  set x₀ := (a+b)/2 with hx₀_def
  have hx₀_mem : x₀ ∈ Set.Ioo a b := by
    refine ⟨by nlinarith, by nlinarith⟩
  have hfx₀_pos : f x₀ > 0 := hf_pos x₀ hx₀_mem
  have h_cont_ax₀ : ContinuousOn f (Set.Icc a x₀) :=
    hf_cont.mono (Set.Icc_subset_Icc (by nlinarith) (by nlinarith))
  have h_zero_in : (0 : ℝ) ∈ Set.Ioo (f a) (f x₀) := ⟨h_neg, hfx₀_pos⟩
  have h_IVT : (0 : ℝ) ∈ f '' Set.Ioo a x₀ :=
    intermediate_value_Ioo (by nlinarith : a ≤ x₀) h_cont_ax₀ h_zero_in
  rcases h_IVT with ⟨c, hc, hc_eq⟩
  rcases hc with ⟨hc1, hc2⟩
  have hc_mem : c ∈ Set.Ioo a b := ⟨hc1, by nlinarith⟩
  have : f c > 0 := hf_pos c hc_mem
  rw [hc_eq] at this
  linarith

lemma pos_at_endpoint' (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf_pos : ∀ x ∈ Set.Ioo a b, f x > 0) (hf_cont : ContinuousOn f (Set.Icc a b)) (hf_nonzero : f b ≠ 0) : f b > 0 := by
  set g := fun x : ℝ => f (a + b - x) with hg
  have hg_pos : ∀ x ∈ Set.Ioo a b, g x > 0 := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    dsimp [g]
    have h1 : a < a + b - x := by nlinarith
    have h2 : a + b - x < b := by nlinarith
    exact hf_pos (a + b - x) ⟨h1, h2⟩
  have hg_cont : ContinuousOn g (Set.Icc a b) := by
    have : ContinuousOn (fun x : ℝ => a + b - x) (Set.Icc a b) :=
      (continuous_const.sub continuous_id).continuousOn
    refine hf_cont.comp this ?_
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have h1 : a ≤ a + b - x := by nlinarith
    have h2 : a + b - x ≤ b := by nlinarith
    exact ⟨h1, h2⟩
  have hg_nonzero : g a ≠ 0 := by
    dsimp [g]; simp [hf_nonzero]
  have hg_pos_a : g a > 0 := pos_at_endpoint g hab hg_pos hg_cont hg_nonzero
  dsimp [g] at hg_pos_a
  have : a + b - a = b := by ring
  rw [this] at hg_pos_a
  exact hg_pos_a

lemma neg_at_endpoint (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf_neg : ∀ x ∈ Set.Ioo a b, f x < 0) (hf_cont : ContinuousOn f (Set.Icc a b)) (hf_nonzero : f a ≠ 0) : f a < 0 := by
  have h_pos_neg : ∀ x ∈ Set.Ioo a b, (-f) x > 0 := by
    intro x hx; simp [hf_neg x hx]
  have h_nonzero_neg : (-f) a ≠ 0 := by
    intro h; apply hf_nonzero; simpa [neg_eq_zero] using h
  have h_cont_neg : ContinuousOn (-f) (Set.Icc a b) := hf_cont.neg
  have h_pos : (-f) a > 0 := pos_at_endpoint (-f) hab h_pos_neg h_cont_neg h_nonzero_neg
  have : (-f) a = -(f a) := rfl
  rw [this] at h_pos
  linarith

lemma neg_at_endpoint' (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf_neg : ∀ x ∈ Set.Ioo a b, f x < 0) (hf_cont : ContinuousOn f (Set.Icc a b)) (hf_nonzero : f b ≠ 0) : f b < 0 := by
  set g := fun x : ℝ => f (a + b - x) with hg
  have hg_neg : ∀ x ∈ Set.Ioo a b, g x < 0 := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    dsimp [g]
    have h1 : a < a + b - x := by nlinarith
    have h2 : a + b - x < b := by nlinarith
    exact hf_neg (a + b - x) ⟨h1, h2⟩
  have hg_cont : ContinuousOn g (Set.Icc a b) := by
    have : ContinuousOn (fun x : ℝ => a + b - x) (Set.Icc a b) :=
      (continuous_const.sub continuous_id).continuousOn
    refine hf_cont.comp this ?_
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have h1 : a ≤ a + b - x := by nlinarith
    have h2 : a + b - x ≤ b := by nlinarith
    exact ⟨h1, h2⟩
  have hg_nonzero : g a ≠ 0 := by
    dsimp [g]; simp [hf_nonzero]
  have hg_neg_a : g a < 0 := neg_at_endpoint g hab hg_neg hg_cont hg_nonzero
  dsimp [g] at hg_neg_a
  have : a + b - a = b := by ring
  rw [this] at hg_neg_a
  exact hg_neg_a

theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  have haJ : a ∈ J := hJ_sub (Set.left_mem_Icc.mpr (by linarith))
  have hbJ : b ∈ J := hJ_sub (Set.right_mem_Icc.mpr (by linarith))
  have hW_nonzero : ∀ x ∈ J, W y₁ y₂ x ≠ 0 := by
    rcases hW with ⟨x₀, hx₀J, hx₀W⟩
    by_contra! h
    rcases h with ⟨x, hxJ, hxW⟩
    have hzero : ∀ x ∈ J, W y₁ y₂ x = 0 :=
      wronskian_zero_of_point p q y₁ y₂ J hJ_open hJ_conn hp hq hy₁ hy₁' hy₂ hy₂' x hxJ hxW
    have : W y₁ y₂ x₀ = 0 := hzero x₀ hx₀J
    exact hx₀W this
  have hWa_nonzero : W y₁ y₂ a ≠ 0 := hW_nonzero a haJ
  have hWb_nonzero : W y₁ y₂ b ≠ 0 := hW_nonzero b hbJ
  have hy₁_cont_ioo : ∀ x ∈ Set.Ioo a b, ContinuousAt y₁ x := by
    intro x hx
    have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx)
    exact (hy₁ x hxJ).continuousAt
  rcases constant_sign_nonzero_cont y₁ a b hab hne hy₁_cont_ioo with (hy₁_pos | hy₁_neg)
  · -- y₁(x) > 0 for all x ∈ (a,b)
    have hy₂a_nonzero : y₂ a ≠ 0 := by
      intro h
      have : W y₁ y₂ a = 0 := by
        unfold W; simp [hza, h]
      exact hWa_nonzero this
    have hy₂b_nonzero : y₂ b ≠ 0 := by
      intro h
      have : W y₁ y₂ b = 0 := by
        unfold W; simp [hzb, h]
      exact hWb_nonzero this
    set r := (b - a) / 2 with hr_def
    have hr_pos : r > 0 := by nlinarith
    have h_pos_near_a : ∀ x ∈ Set.Ioo a (a + r), y₁ x > 0 := by
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      have : x ∈ Set.Ioo a b := ⟨hx1, by dsimp [r] at hx2; nlinarith⟩
      exact hy₁_pos x this
    have h_pos_near_b : ∀ x ∈ Set.Ioo (b - r) b, y₁ x > 0 := by
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      have : x ∈ Set.Ioo a b := ⟨by dsimp [r] at hx1; nlinarith, hx2⟩
      exact hy₁_pos x this
    have hy₁_deriv_a_nonneg : 0 ≤ deriv y₁ a :=
      deriv_nonneg_of_pos_on_interval y₁ hr_pos h_pos_near_a hza (hy₁ a haJ)
    have hy₁_deriv_a_pos : 0 < deriv y₁ a := by
      by_contra! h
      have : deriv y₁ a = 0 := by linarith
      have : W y₁ y₂ a = 0 := by
        unfold W; rw [hza, this]; simp
      exact hWa_nonzero this
    have hy₁_deriv_b_nonpos : deriv y₁ b ≤ 0 :=
      deriv_nonpos_of_pos_on_interval y₁ hr_pos h_pos_near_b hzb (hy₁ b hbJ)
    have hy₁_deriv_b_neg : deriv y₁ b < 0 := by
      by_contra! h
      have : deriv y₁ b = 0 := by linarith
      have : W y₁ y₂ b = 0 := by
        unfold W; rw [hzb, this]; simp
      exact hWb_nonzero this
    have hW_cont_ioo : ∀ x ∈ Set.Ioo a b, ContinuousAt (W y₁ y₂) x := by
      intro x hx
      have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx)
      have hderiv := wronskian_deriv p q y₁ y₂ x (hy₁ x hxJ) (hy₁' x hxJ) (hy₂ x hxJ) (hy₂' x hxJ)
      exact hderiv.continuousAt
    have hW_nonzero_ioo : ∀ x ∈ Set.Ioo a b, W y₁ y₂ x ≠ 0 := by
      intro x hx
      exact hW_nonzero x (hJ_sub (Set.mem_Icc_of_Ioo hx))
    have hW_cont_cc : ContinuousOn (W y₁ y₂) (Set.Icc a b) := by
      intro x hx
      have hxJ : x ∈ J := hJ_sub hx
      have hderiv := wronskian_deriv p q y₁ y₂ x (hy₁ x hxJ) (hy₁' x hxJ) (hy₂ x hxJ) (hy₂' x hxJ)
      exact hderiv.continuousAt.continuousWithinAt
    rcases constant_sign_nonzero_cont (W y₁ y₂) a b hab hW_nonzero_ioo hW_cont_ioo with (hW_pos | hW_neg)
    · -- W > 0 on (a,b). Then y₂(a) < 0 and y₂(b) > 0
      have hWa_pos : W y₁ y₂ a > 0 := pos_at_endpoint (W y₁ y₂) hab hW_pos hW_cont_cc hWa_nonzero
      have hWb_pos : W y₁ y₂ b > 0 := pos_at_endpoint' (W y₁ y₂) hab hW_pos hW_cont_cc hWb_nonzero
      have hy₂a_neg : y₂ a < 0 := by
        have hWa_eq : W y₁ y₂ a = -(y₂ a) * deriv y₁ a := by
          unfold W; rw [hza]; ring
        rw [hWa_eq] at hWa_pos
        nlinarith
      have hy₂b_pos : y₂ b > 0 := by
        have hWb_eq : W y₁ y₂ b = -(y₂ b) * deriv y₁ b := by
          unfold W; rw [hzb]; ring
        rw [hWb_eq] at hWb_pos
        nlinarith
      have h_exists : ∃ c ∈ Set.Ioo a b, y₂ c = 0 := by
        have h_cont_y₂ : ContinuousOn y₂ (Set.Icc a b) := by
          intro x hx
          have hxJ : x ∈ J := hJ_sub hx
          exact (hy₂ x hxJ).continuousAt.continuousWithinAt
        have h0_in : (0 : ℝ) ∈ Set.Ioo (y₂ a) (y₂ b) := ⟨hy₂a_neg, hy₂b_pos⟩
        have h_IVT : (0 : ℝ) ∈ y₂ '' Set.Ioo a b :=
          intermediate_value_Ioo (by nlinarith : a ≤ b) h_cont_y₂ h0_in
        rcases h_IVT with ⟨c, hc, hc_eq⟩
        exact ⟨c, hc, hc_eq⟩
      -- Uniqueness: the quotient y₂/y₁ is strictly monotone on (a,b), hence injective
      have h_unique : ∀ (c₁ c₂ : ℝ), c₁ ∈ Set.Ioo a b → y₂ c₁ = 0 → c₂ ∈ Set.Ioo a b → y₂ c₂ = 0 → c₁ = c₂ := by
        intro u v hu hu_eq hv hv_eq
        by_cases hlt : u < v
        · exfalso
          have h_cont_r : ContinuousOn (fun x => y₂ x / y₁ x) (Set.Icc u v) := by
            intro x hx
            rcases hx with ⟨hx1, hx2⟩
            have hx_ioo : x ∈ Set.Ioo a b := by
              rcases hu with ⟨hua, hub⟩
              rcases hv with ⟨hva, hvb⟩
              refine ⟨by nlinarith, by nlinarith⟩
            have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx_ioo)
            have hy₁x_ne_zero : y₁ x ≠ 0 := hne x hx_ioo
            have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ x / (y₁ x)^2) x :=
              HasDerivAt.div (hy₂ x hxJ) (hy₁ x hxJ) hy₁x_ne_zero
            exact h_deriv_quot.continuousAt.continuousWithinAt
          have h_eq : (fun x => y₂ x / y₁ x) u = (fun x => y₂ x / y₁ x) v := by
            simp [hu_eq, hv_eq]
          have h_rolle : ∃ ξ ∈ Set.Ioo u v, deriv (fun x => y₂ x / y₁ x) ξ = 0 :=
            exists_deriv_eq_zero hlt h_cont_r h_eq
          rcases h_rolle with ⟨ξ, hξ, hξ_eq⟩
          have hξ_ioo : ξ ∈ Set.Ioo a b := by
            rcases hξ with ⟨hξ1, hξ2⟩
            rcases hu with ⟨hua, hub⟩
            rcases hv with ⟨hva, hvb⟩
            refine ⟨by nlinarith, by nlinarith⟩
          have hWξ_nonzero : W y₁ y₂ ξ ≠ 0 := hW_nonzero_ioo ξ hξ_ioo
          have hy₁ξ_pos : y₁ ξ > 0 := hy₁_pos ξ hξ_ioo
          have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ ξ / (y₁ ξ)^2) ξ := by
            have hxJ : ξ ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hξ_ioo)
            have hy₁ξ_ne_zero : y₁ ξ ≠ 0 := hne ξ hξ_ioo
            exact HasDerivAt.div (hy₂ ξ hxJ) (hy₁ ξ hxJ) hy₁ξ_ne_zero
          have h_deriv_nonzero : deriv (fun x' => y₂ x' / y₁ x') ξ ≠ 0 := by
            rw [h_deriv_quot.deriv]
            refine div_ne_zero hWξ_nonzero (by positivity)
          exact h_deriv_nonzero hξ_eq
        · by_cases hlt2 : v < u
          · exfalso
            have h_cont_r : ContinuousOn (fun x => y₂ x / y₁ x) (Set.Icc v u) := by
              intro x hx
              rcases hx with ⟨hx1, hx2⟩
              have hx_ioo : x ∈ Set.Ioo a b := by
                rcases hu with ⟨hua, hub⟩
                rcases hv with ⟨hva, hvb⟩
                refine ⟨by nlinarith, by nlinarith⟩
              have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx_ioo)
              have hy₁x_ne_zero : y₁ x ≠ 0 := hne x hx_ioo
              have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ x / (y₁ x)^2) x :=
                HasDerivAt.div (hy₂ x hxJ) (hy₁ x hxJ) hy₁x_ne_zero
              exact h_deriv_quot.continuousAt.continuousWithinAt
            have h_eq : (fun x => y₂ x / y₁ x) v = (fun x => y₂ x / y₁ x) u := by
              simp [hu_eq, hv_eq]
            have h_rolle : ∃ ξ ∈ Set.Ioo v u, deriv (fun x => y₂ x / y₁ x) ξ = 0 :=
              exists_deriv_eq_zero hlt2 h_cont_r h_eq
            rcases h_rolle with ⟨ξ, hξ, hξ_eq⟩
            have hξ_ioo : ξ ∈ Set.Ioo a b := by
              rcases hξ with ⟨hξ1, hξ2⟩
              rcases hu with ⟨hua, hub⟩
              rcases hv with ⟨hva, hvb⟩
              refine ⟨by nlinarith, by nlinarith⟩
            have hWξ_nonzero : W y₁ y₂ ξ ≠ 0 := hW_nonzero_ioo ξ hξ_ioo
            have hy₁ξ_pos : y₁ ξ > 0 := hy₁_pos ξ hξ_ioo
            have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ ξ / (y₁ ξ)^2) ξ := by
              have hxJ : ξ ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hξ_ioo)
              have hy₁ξ_ne_zero : y₁ ξ ≠ 0 := hne ξ hξ_ioo
              exact HasDerivAt.div (hy₂ ξ hxJ) (hy₁ ξ hxJ) hy₁ξ_ne_zero
            have h_deriv_nonzero : deriv (fun x' => y₂ x' / y₁ x') ξ ≠ 0 := by
              rw [h_deriv_quot.deriv]
              refine div_ne_zero hWξ_nonzero (by positivity)
            exact h_deriv_nonzero hξ_eq
          · linarith
      rcases h_exists with ⟨c, hc, hc_eq⟩
      refine ⟨c, hc, hc_eq, ?_⟩
      intro d hd
      rcases hd with ⟨hd_ioo, hd_eq⟩
      exact h_unique c hc hc_eq d hd_ioo hd_eq
    · -- W < 0 on (a,b). Then y₂(a) > 0 and y₂(b) < 0
      have hWa_neg : W y₁ y₂ a < 0 := neg_at_endpoint (W y₁ y₂) hab hW_neg hW_cont_cc hWa_nonzero
      have hWb_neg : W y₁ y₂ b < 0 := neg_at_endpoint' (W y₁ y₂) hab hW_neg hW_cont_cc hWb_nonzero
      have hy₂a_pos : y₂ a > 0 := by
        have hWa_eq : W y₁ y₂ a = -(y₂ a) * deriv y₁ a := by
          unfold W; rw [hza]; ring
        rw [hWa_eq] at hWa_neg
        nlinarith
      have hy₂b_neg : y₂ b < 0 := by
        have hWb_eq : W y₁ y₂ b = -(y₂ b) * deriv y₁ b := by
          unfold W; rw [hzb]; ring
        rw [hWb_eq] at hWb_neg
        nlinarith
      have h_exists : ∃ c ∈ Set.Ioo a b, y₂ c = 0 := by
        have h_cont_y₂ : ContinuousOn y₂ (Set.Icc a b) := by
          intro x hx
          have hxJ : x ∈ J := hJ_sub hx
          exact (hy₂ x hxJ).continuousAt.continuousWithinAt
        have h0_in : (0 : ℝ) ∈ Set.Ioo (y₂ b) (y₂ a) := ⟨hy₂b_neg, hy₂a_pos⟩
        have h_IVT : (0 : ℝ) ∈ y₂ '' Set.Ioo a b :=
          intermediate_value_Ioo' (by nlinarith : a ≤ b) h_cont_y₂ h0_in
        rcases h_IVT with ⟨c, hc, hc_eq⟩
        exact ⟨c, hc, hc_eq⟩
      have h_unique : ∀ (c₁ c₂ : ℝ), c₁ ∈ Set.Ioo a b → y₂ c₁ = 0 → c₂ ∈ Set.Ioo a b → y₂ c₂ = 0 → c₁ = c₂ := by
        intro u v hu hu_eq hv hv_eq
        by_cases hlt : u < v
        · exfalso
          have h_cont_r : ContinuousOn (fun x => y₂ x / y₁ x) (Set.Icc u v) := by
            intro x hx
            rcases hx with ⟨hx1, hx2⟩
            have hx_ioo : x ∈ Set.Ioo a b := by
              rcases hu with ⟨hua, hub⟩
              rcases hv with ⟨hva, hvb⟩
              refine ⟨by nlinarith, by nlinarith⟩
            have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx_ioo)
            have hy₁x_ne_zero : y₁ x ≠ 0 := hne x hx_ioo
            have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ x / (y₁ x)^2) x :=
              HasDerivAt.div (hy₂ x hxJ) (hy₁ x hxJ) hy₁x_ne_zero
            exact h_deriv_quot.continuousAt.continuousWithinAt
          have h_eq : (fun x => y₂ x / y₁ x) u = (fun x => y₂ x / y₁ x) v := by
            simp [hu_eq, hv_eq]
          have h_rolle : ∃ ξ ∈ Set.Ioo u v, deriv (fun x => y₂ x / y₁ x) ξ = 0 :=
            exists_deriv_eq_zero hlt h_cont_r h_eq
          rcases h_rolle with ⟨ξ, hξ, hξ_eq⟩
          have hξ_ioo : ξ ∈ Set.Ioo a b := by
            rcases hξ with ⟨hξ1, hξ2⟩
            rcases hu with ⟨hua, hub⟩
            rcases hv with ⟨hva, hvb⟩
            refine ⟨by nlinarith, by nlinarith⟩
          have hWξ_nonzero : W y₁ y₂ ξ ≠ 0 := hW_nonzero_ioo ξ hξ_ioo
          have hy₁ξ_pos : y₁ ξ > 0 := hy₁_pos ξ hξ_ioo
          have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ ξ / (y₁ ξ)^2) ξ := by
            have hxJ : ξ ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hξ_ioo)
            have hy₁ξ_ne_zero : y₁ ξ ≠ 0 := hne ξ hξ_ioo
            exact HasDerivAt.div (hy₂ ξ hxJ) (hy₁ ξ hxJ) hy₁ξ_ne_zero
          have h_deriv_nonzero : deriv (fun x' => y₂ x' / y₁ x') ξ ≠ 0 := by
            rw [h_deriv_quot.deriv]
            refine div_ne_zero hWξ_nonzero (by positivity)
          exact h_deriv_nonzero hξ_eq
        · by_cases hlt2 : v < u
          · exfalso
            have h_cont_r : ContinuousOn (fun x => y₂ x / y₁ x) (Set.Icc v u) := by
              intro x hx
              rcases hx with ⟨hx1, hx2⟩
              have hx_ioo : x ∈ Set.Ioo a b := by
                rcases hu with ⟨hua, hub⟩
                rcases hv with ⟨hva, hvb⟩
                refine ⟨by nlinarith, by nlinarith⟩
              have hxJ : x ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hx_ioo)
              have hy₁x_ne_zero : y₁ x ≠ 0 := hne x hx_ioo
              have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ x / (y₁ x)^2) x :=
                HasDerivAt.div (hy₂ x hxJ) (hy₁ x hxJ) hy₁x_ne_zero
              exact h_deriv_quot.continuousAt.continuousWithinAt
            have h_eq : (fun x => y₂ x / y₁ x) v = (fun x => y₂ x / y₁ x) u := by
              simp [hu_eq, hv_eq]
            have h_rolle : ∃ ξ ∈ Set.Ioo v u, deriv (fun x => y₂ x / y₁ x) ξ = 0 :=
              exists_deriv_eq_zero hlt2 h_cont_r h_eq
            rcases h_rolle with ⟨ξ, hξ, hξ_eq⟩
            have hξ_ioo : ξ ∈ Set.Ioo a b := by
              rcases hξ with ⟨hξ1, hξ2⟩
              rcases hu with ⟨hua, hub⟩
              rcases hv with ⟨hva, hvb⟩
              refine ⟨by nlinarith, by nlinarith⟩
            have hWξ_nonzero : W y₁ y₂ ξ ≠ 0 := hW_nonzero_ioo ξ hξ_ioo
            have hy₁ξ_pos : y₁ ξ > 0 := hy₁_pos ξ hξ_ioo
            have h_deriv_quot : HasDerivAt (fun x' => y₂ x' / y₁ x') (W y₁ y₂ ξ / (y₁ ξ)^2) ξ := by
              have hxJ : ξ ∈ J := hJ_sub (Set.mem_Icc_of_Ioo hξ_ioo)
              have hy₁ξ_ne_zero : y₁ ξ ≠ 0 := hne ξ hξ_ioo
              exact HasDerivAt.div (hy₂ ξ hxJ) (hy₁ ξ hxJ) hy₁ξ_ne_zero
            have h_deriv_nonzero : deriv (fun x' => y₂ x' / y₁ x') ξ ≠ 0 := by
              rw [h_deriv_quot.deriv]
              refine div_ne_zero hWξ_nonzero (by positivity)
            exact h_deriv_nonzero hξ_eq
          · linarith
      rcases h_exists with ⟨c, hc, hc_eq⟩
      refine ⟨c, hc, hc_eq, ?_⟩
      intro d hd
      rcases hd with ⟨hd_ioo, hd_eq⟩
      exact h_unique c hc hc_eq d hd_ioo hd_eq
  · -- y₁(x) < 0 for all x ∈ (a,b). Replace y₁ by -y₁ and apply the y₁ > 0 case.
    have hne' : ∀ x ∈ Set.Ioo a b, (-y₁) x ≠ 0 := by
      intro x hx; simp [hy₁_neg x hx]
    have hza' : (-y₁) a = 0 := by simp [hza]
    have hzb' : (-y₁) b = 0 := by simp [hzb]
    have h_cont_ioo' : ∀ x ∈ Set.Ioo a b, ContinuousAt (-y₁) x := by
      intro x hx; exact (hy₁_cont_ioo x hx).neg
    rcases constant_sign_nonzero_cont (-y₁) a b hab hne' h_cont_ioo' with (hpos' | hneg')
    · -- -y₁ > 0 on (a,b), so apply the y₁ > 0 case to (-y₁, y₂)
      have hW' : ∃ x₀ ∈ J, (-y₁) x₀ * deriv y₂ x₀ - y₂ x₀ * deriv (-y₁) x₀ ≠ 0 := by
        rcases hW with ⟨x₀, hx₀J, hx₀W⟩
        refine ⟨x₀, hx₀J, ?_⟩
        have : deriv (-y₁) x₀ = -deriv y₁ x₀ := deriv_neg _ _
        simp [this, hx₀W]
      have hy₁''_neg : ∀ x ∈ J, HasDerivAt (deriv (-y₁)) (-(p x * deriv (-y₁) x + q x * (-y₁) x)) x := by
        intro x hx
        have h : HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x := hy₁' x hx
        have h_deriv_neg' : HasDerivAt (deriv (-y₁)) (-(p x * (-deriv y₁ x) + q x * (-y₁ x))) x := by
          simpa [deriv_neg] using HasDerivAt.neg h
        have : -(p x * (-deriv y₁ x) + q x * (-y₁ x)) = -(p x * deriv (-y₁) x + q x * (-y₁) x) := by
          simp [deriv_neg]
        rw [this]
        simpa [deriv_neg] using h_deriv_neg'
      exact sturm_separation p q (-y₁) y₂ a b hab J hJ_open hJ_conn hJ_sub hp hq
        (fun x hx => HasDerivAt.neg (hy₁ x hx)) hy₁''_neg hy₂ hy₂' hW' hza' hzb' hne'
    · -- -y₁ < 0 on (a,b), which means y₁ > 0, contradicting hy₁_neg
      exfalso
      have hx : (a+b)/2 ∈ Set.Ioo a b := by nlinarith
      have : (-y₁) ((a+b)/2) > 0 := hpos' ((a+b)/2) hx
      have : (-y₁) ((a+b)/2) < 0 := hneg' ((a+b)/2) hx
      linarith
end Submission
