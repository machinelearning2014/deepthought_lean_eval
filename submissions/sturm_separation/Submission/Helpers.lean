import Mathlib

namespace Submission.Helpers

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

end Submission.Helpers
