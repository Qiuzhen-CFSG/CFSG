module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.Geometry
public import Theory.GroupTheory.Amalgam.NormalBaseRecognition
public import CFSG.Quasithin.Chapter5.Section03GreenExtension

/-!
# Full Ree normalizer diagrams from the native common action

Normal-supplement gluing extends the marked native parabolic inner maps and
the faithful action of the whole common normalizer. Exact inner preimages
make both maps faithful. Their whole overlap and native inner intersections
produce the genuine F.4.3 extension. This is algebraic gluing, without any
ambient order or recognition hypothesis.

The argument specializes the checked normal-supplement construction in
Chapter5.Section03SymplecticSource.Endpoint, retaining the native Ree pair.
Source: Aschbacher–Smith 5.3.2 and F.4.3, printed pp.659,274.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4.Parabolics
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
variable {G N : Type*} [Group G] [Group N]

private theorem glue_endpoint (hconj : Function.Injective (MulAut.conj : N →* MulAut N)) (P M D : Subgroup G)
    (hPM : P ≤ M) (hDM : D ≤ M) (hn : M ≤ normalizer (P : Set G))
    (hg : M = P ⊔ D)
    (R : Subgroup (N)) (e : P ≃* R)
    (ρ : D →* MulAut (N))
    (hi : ∀ d : D, ρ d ∈ R.map MulAut.conj ↔ d.val ∈ P)
    (ha : ∀ (d : D) (hd : d.val ∈ P), MulAut.conj (e ⟨d.val,hd⟩).val = ρ d)
    (hc : ∀ (d : D) (x : P), ∃ hx : d.val*x.val*d.val⁻¹ ∈ P,
      (e ⟨d.val*x.val*d.val⁻¹,hx⟩).val = ρ d (e x).val) :
    ∃ f : M →* MulAut (N), Function.Injective f ∧
      (∀ x : P, f (inclusion hPM x) = MulAut.conj (e x).val) ∧
      (∀ d : D, f (inclusion hDM d) = ρ d) ∧
      f.range = R.map MulAut.conj ⊔ ρ.range := by
  let U := P.subgroupOf M
  let T := D.subgroupOf M
  let : U.Normal := (normal_subgroupOf_iff_le_normalizer hPM).mpr hn
  let z : U ≃* R.map (MulAut.conj : N →* MulAut N) :=
    (subgroupOfEquivOfLe hPM).trans
      (e.trans (R.equivMapOfInjective MulAut.conj (hconj)))
  let v : T →* MulAut (N) := ρ.comp (subgroupOfEquivOfLe hDM).toMonoidHom
  have hv : v.range = ρ.range := by
    ext a
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨subgroupOfEquivOfLe hDM t,rfl⟩
    · rintro ⟨d,rfl⟩
      exact ⟨(subgroupOfEquivOfLe hDM).symm d, rfl⟩
  have hgen : U ⊔ T = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hPM, map_subgroupOf_eq_of_le hDM,
      ←MonoidHom.range_eq_map, range_subtype, ←hg]
  obtain ⟨f,hf,hv'⟩ := RankTwoAmalgam.NormalBaseRecognition.exists_endpoint_equiv U T
    (R.map MulAut.conj) z v hgen (fun t => hi (subgroupOfEquivOfLe hDM t))
    (fun t ht => ha (subgroupOfEquivOfLe hDM t) ht) (by
      intro t x
      obtain ⟨hx,he⟩ := hc (subgroupOfEquivOfLe hDM t) (subgroupOfEquivOfLe hPM x)
      change MulAut.conj (e ⟨_,_⟩).val = ρ _ * MulAut.conj (e _).val * (ρ _)⁻¹
      have he' : (e ⟨((MulAut.conjNormal (t.val : M) x).val : G),
          (MulAut.conjNormal (t.val : M) x).property⟩).val =
          ρ (subgroupOfEquivOfLe hDM t) (e (subgroupOfEquivOfLe hPM x)).val := by
        refine Eq.trans ?_ he
        apply congrArg (fun y : P => (e y).val)
        apply Subtype.ext
        exact congrArg (fun y : M => (y : G)) (MulAut.conjNormal_apply (t.val : M) x)
      rw [he']
      ext y
      simp)
  let f' := (R.map MulAut.conj ⊔ v.range).subtype.comp f.toMonoidHom
  refine ⟨f', Subtype.val_injective.comp f.injective, ?_, ?_, ?_⟩
  · intro x
    exact hf ((subgroupOfEquivOfLe hPM).symm x)
  · intro d
    exact hv' ((subgroupOfEquivOfLe hDM).symm d)
  · rw [show f'.range = R.map MulAut.conj ⊔ v.range from ?_, hv]
    rw [MonoidHom.range_comp, show f.toMonoidHom.range = ⊤ from MonoidHom.range_eq_top.mpr f.surjective,
      ←MonoidHom.range_eq_map, range_subtype]


private theorem normalized_of_action (P D : Subgroup G)
    (R : Subgroup (N)) (e : P ≃* R) (ρ : D →* MulAut (N))
    (hc : ∀ (d : D) (x : P), ∃ hx : d.val*x.val*d.val⁻¹ ∈ P,
      (e ⟨d.val*x.val*d.val⁻¹,hx⟩).val = ρ d (e x).val) :
    D ≤ normalizer (P : Set G) := by
  intro d hd
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    exact (hc ⟨d,hd⟩ ⟨x,hx⟩).choose
  · intro hx
    have hh := (hc (⟨d,hd⟩ : D)⁻¹ ⟨d*x*d⁻¹,hx⟩).choose
    simpa only [InvMemClass.coe_inv, inv_inv, inv_mul_cancel_left,
      mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using hh

private theorem endpoint_of_lift (hconj : Function.Injective (MulAut.conj : N →* MulAut N)) (P M D C : Subgroup G)
    (hPM : P ≤ M) (hDM : D ≤ M) (hPD : P ⊓ D = C)
    (hprod : ∀ x ∈ M, ∃ p ∈ P, ∃ d ∈ D, x = p*d)
    (R : Subgroup (N)) (e : P ≃* R) (ρ : D →* MulAut (N))
    (hi : ∀ d : D, ρ d ∈ UnitaryNonbinary.inner (N) ↔ d.val ∈ C)
    (ha : ∀ (d : D) (hd : d.val ∈ C), MulAut.conj (e ⟨d.val,(hPD.ge hd).1⟩).val = ρ d)
    (hc : ∀ (d : D) (x : P), ∃ hx : d.val*x.val*d.val⁻¹ ∈ P,
      (e ⟨d.val*x.val*d.val⁻¹,hx⟩).val = ρ d (e x).val) :
    ∃ f : M →* MulAut (N), Function.Injective f ∧
      (∀ x : P, f (inclusion hPM x) = MulAut.conj (e x).val) ∧
      (∀ d : D, f (inclusion hDM d) = ρ d) ∧
      f.range = R.map MulAut.conj ⊔ ρ.range := by
  have hg : M = P ⊔ D := by
    apply le_antisymm _ (sup_le hPM hDM)
    intro x hx
    obtain ⟨p,hp,d,hd,rfl⟩ := hprod x hx
    exact Subgroup.mul_mem_sup hp hd
  apply glue_endpoint hconj P M D hPM hDM
    (by rw [hg]; exact sup_le P.le_normalizer (normalized_of_action P D R e ρ hc))
    hg R e ρ
  · intro d
    constructor
    · intro hd
      exact (hPD.ge ((hi d).mp (Subgroup.map_le_range _ _ hd))).1
    · intro hd
      have hb := hPD.le ⟨hd,d.property⟩
      rw [←ha d hb]
      exact ⟨_,(e ⟨d.val,hd⟩).property,rfl⟩
  · intro d hd
    exact ha d (hPD.le ⟨hd,d.property⟩)
  · exact hc

/-- A faithful common action on an abstract native carrier extends across both full endpoints. The
whole common intersection and both pure markings are retained. Keeping the
carrier abstract prevents expensive native matrix-instance conversion. -/
theorem extension_of_lift (hconj : Function.Injective (MulAut.conj : N →* MulAut N)) (R₀ B₀ R₁ : Subgroup N)
    (hB₀ : B₀ ≤ R₀) (hB₁ : B₀ ≤ R₁) (hgen : R₀ ⊔ R₁ = ⊤)
    (hoverlap : R₀ ⊓ R₁ = B₀) (P Q M₁ M₂ D C : Subgroup G)
    (hPM : P ≤ M₁) (hQM : Q ≤ M₂) (hD₁ : D ≤ M₁) (hD₂ : D ≤ M₂)
    (hCD : C ≤ D) (hPD : P ⊓ D = C) (hQD : Q ⊓ D = C)
    (hprod₁ : ∀ x ∈ M₁, ∃ p ∈ P, ∃ d ∈ D, x = p*d)
    (hprod₂ : ∀ x ∈ M₂, ∃ q ∈ Q, ∃ d ∈ D, x = q*d)
    (eP : P ≃* R₀)
    (eQ : Q ≃* R₁) (eC : C ≃* B₀)
    (hPC : ∀ c : C, (eP ⟨c.val,(hPD.ge c.property).1⟩).val = (eC c).val)
    (hQC : ∀ c : C, (eQ ⟨c.val,(hQD.ge c.property).1⟩).val = (eC c).val)
    (σ : D →* MulAut (N)) (hσ : Function.Injective σ)
    (hs : ∀ d : D, (R₀).map (σ d).toMonoidHom = R₀ ∧
      (R₁).map (σ d).toMonoidHom = R₁)
    (hi : ∀ d : D, σ d ∈ UnitaryNonbinary.inner (N) ↔ d.val ∈ C)
    (ha : ∀ c : C, σ (inclusion hCD c) = MulAut.conj (eC c).val)
    (hcP : ∀ (d : D) (x : P), ∃ hx : d.val*x.val*d.val⁻¹ ∈ P,
      (eP ⟨d.val*x.val*d.val⁻¹,hx⟩).val = σ d (eP x).val)
    (hcQ : ∀ (d : D) (x : Q), ∃ hx : d.val*x.val*d.val⁻¹ ∈ Q,
      (eQ ⟨d.val*x.val*d.val⁻¹,hx⟩).val = σ d (eQ x).val) :
    ∃ E : UnitaryNonbinary.SourceExtension R₀ R₁,
      ∃ e : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups M₁ D M₂ hD₁ hD₂) E.amalgam,
        (∀ x : P, (e.left (inclusion hPM x)).val = MulAut.conj (eP x).val) ∧
        (∀ x : Q, (e.right (inclusion hQM x)).val = MulAut.conj (eQ x).val) ∧
        (∀ d : D, (e.middle d).val = σ d) := by
  let ρ := σ
  obtain ⟨f,hf,hfP,hfD,hfr⟩ := endpoint_of_lift hconj P M₁ D C hPM hD₁ hPD hprod₁
    (R₀) eP ρ hi (by
      intro d hd
      rw [hPC ⟨d.val,hd⟩]
      exact (ha ⟨d.val,hd⟩).symm) hcP
  obtain ⟨g,hg,hgQ,hgD,hgr⟩ := endpoint_of_lift hconj Q M₂ D C hQM hD₂ hQD hprod₂
    (R₁) eQ ρ hi (by
      intro d hd
      rw [hQC ⟨d.val,hd⟩]
      exact (ha ⟨d.val,hd⟩).symm) hcQ
  let α : Chapter5.Section03GreenExtension.LieAmalgam (N) :=
    ⟨R₀,B₀,R₁,hB₀,
      hB₁,hgen⟩
  let γ : Chapter5.Section03GreenExtension.LocalAmalgam G := ⟨M₁,D,M₂,hD₁,hD₂⟩
  let a : Chapter5.Section03GreenExtension.CompatibleLocalActions α γ :=
    { left := f
      right := g
      middle := ρ
      left_injective := hf
      right_injective := hg
      middle_injective := hσ
      leftContains := by rw [hfr]; exact le_sup_left
      rightContains := by rw [hgr]; exact le_sup_left
      middle_left_range := by rw [hfr]; exact le_sup_right
      middle_right_range := by rw [hgr]; exact le_sup_right
      left_agrees := hfD
      right_agrees := hgD }
  have hmid : ρ.range ⊓ UnitaryNonbinary.inner (N) = (B₀).map (MulAut.conj : N →* MulAut (N)) := by
    apply le_antisymm
    · rintro _ ⟨⟨d,rfl⟩,hd⟩
      have hb := (hi d).mp hd
      rw [show ρ d = MulAut.conj (eC ⟨d.val,hb⟩).val from ha ⟨d.val,hb⟩]
      exact ⟨_,(eC ⟨d.val,hb⟩).property,rfl⟩
    · rintro _ ⟨b,hb,rfl⟩
      refine ⟨⟨inclusion hCD (eC.symm ⟨b,hb⟩),?_⟩,⟨b,rfl⟩⟩
      change σ (inclusion hCD _) = _
      rw [ha,eC.apply_symm_apply]
  have hp₁ (x : M₁) : ∃ p ∈ R₀, ∃ d : D,
      f x = MulAut.conj p * ρ d := by
    obtain ⟨p,hp,d,hd,he⟩ := hprod₁ x.val x.property
    refine ⟨(eP ⟨p,hp⟩).val,(eP ⟨p,hp⟩).property,⟨d,hd⟩,?_⟩
    have hx : x = inclusion hPM ⟨p,hp⟩ * inclusion hD₁ ⟨d,hd⟩ := Subtype.ext he
    rw [hx,map_mul,hfP,hfD]
  have hp₂ (x : M₂) : ∃ p ∈ R₁, ∃ d : D,
      g x = MulAut.conj p * ρ d := by
    obtain ⟨p,hp,d,hd,he⟩ := hprod₂ x.val x.property
    refine ⟨(eQ ⟨p,hp⟩).val,(eQ ⟨p,hp⟩).property,⟨d,hd⟩,?_⟩
    have hx : x = inclusion hQM ⟨p,hp⟩ * inclusion hD₂ ⟨d,hd⟩ := Subtype.ext he
    rw [hx,map_mul,hgQ,hgD]
  obtain ⟨hl,hr,hm⟩ := a.intersections (hconj)
    hoverlap hmid hp₁ hp₂
  let E : UnitaryNonbinary.SourceExtension R₀ R₁ :=
    { carrier := a.completion
      left := f.range
      right := g.range
      left_le := le_sup_left
      right_le := le_sup_right
      contains_inner := a.inner_le_completion
      left_inner := hl
      right_inner := hr
      factor := by
        intro z hz
        obtain ⟨x,d,rfl⟩ := (a.completion_product hp₁ hp₂ z).mp hz
        exact ⟨x,ρ d,hm.ge ⟨d,rfl⟩,rfl⟩
      preserves_types := by
        intro z hz
        obtain ⟨x,d,rfl⟩ := (a.completion_product hp₁ hp₂ z).mp hz
        constructor
        · refine ⟨x,?_⟩
          change (R₀).map ((MulAut.conj x).toMonoidHom.comp (ρ d).toMonoidHom) = _
          rw [←Subgroup.map_map]
          exact congrArg (fun U => U.map (MulAut.conj x).toMonoidHom)
            (hs d).1
        · refine ⟨x,?_⟩
          change (R₁).map ((MulAut.conj x).toMonoidHom.comp (ρ d).toMonoidHom) = _
          rw [←Subgroup.map_map]
          exact congrArg (fun U => U.map (MulAut.conj x).toMonoidHom)
            (hs d).2 }
  let e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups M₁ D M₂ hD₁ hD₂) E.amalgam :=
    { left := MonoidHom.ofInjective hf
      right := MonoidHom.ofInjective hg
      middle := (MonoidHom.ofInjective (hσ)).trans
        (MulEquiv.subgroupCongr hm.symm)
      left_commutes d := Subtype.ext (hfD d)
      right_commutes d := Subtype.ext (hgD d) }
  exact ⟨E,e,hfP,hgQ,fun _ => rfl⟩

variable {m : ℕ}

/-- A faithful native middle lift extends across both full endpoints. The
whole common intersection and both pure markings are retained. -/
theorem extension_of_native_lift (hm : 0 < m) (P Q M₁ M₂ D C : Subgroup G)
    (hPM : P ≤ M₁) (hQM : Q ≤ M₂) (hD₁ : D ≤ M₁) (hD₂ : D ≤ M₂)
    (hCD : C ≤ D) (hPD : P ⊓ D = C) (hQD : Q ⊓ D = C)
    (hprod₁ : ∀ x ∈ M₁, ∃ p ∈ P, ∃ d ∈ D, x = p*d)
    (hprod₂ : ∀ x ∈ M₂, ∃ q ∈ Q, ∃ d ∈ D, x = q*d)
    (eP : P ≃* parabolic m .linear)
    (eQ : Q ≃* parabolic m .suzuki) (eC : C ≃* borel m)
    (hPC : ∀ c : C, (eP ⟨c.val,(hPD.ge c.property).1⟩).val = (eC c).val)
    (hQC : ∀ c : C, (eQ ⟨c.val,(hQD.ge c.property).1⟩).val = (eC c).val)
    (σ : D →* MulAut (ReeF4.Model m)) (hσ : Function.Injective σ)
    (hs : ∀ d : D, (parabolic m .linear).map (σ d).toMonoidHom = parabolic m .linear ∧
      (parabolic m .suzuki).map (σ d).toMonoidHom = parabolic m .suzuki)
    (hi : ∀ d : D, σ d ∈ UnitaryNonbinary.inner (ReeF4.Model m) ↔ d.val ∈ C)
    (ha : ∀ c : C, σ (inclusion hCD c) = MulAut.conj (eC c).val)
    (hcP : ∀ (d : D) (x : P), ∃ hx : d.val*x.val*d.val⁻¹ ∈ P,
      (eP ⟨d.val*x.val*d.val⁻¹,hx⟩).val = σ d (eP x).val)
    (hcQ : ∀ (d : D) (x : Q), ∃ hx : d.val*x.val*d.val⁻¹ ∈ Q,
      (eQ ⟨d.val*x.val*d.val⁻¹,hx⟩).val = σ d (eQ x).val) :
    ∃ E : GeneralReeExtension.SourceExtension m,
      ∃ e : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups M₁ D M₂ hD₁ hD₂) E.amalgam,
        (∀ x : P, (e.left (inclusion hPM x)).val = MulAut.conj (eP x).val) ∧
        (∀ x : Q, (e.right (inclusion hQM x)).val = MulAut.conj (eQ x).val) ∧
        (∀ d : D, (e.middle d).val = σ d) := by
  exact extension_of_lift (ReeF4.SmallCompletion.conj_injective m hm)
    (parabolic m .linear) (borel m) (parabolic m .suzuki)
    (borel_le_parabolic m .linear) (borel_le_parabolic m .suzuki)
    (by rw [sup_comm]; exact GreenBook.LieModels.ReeFour.parabolics_generate m)
    (by rw [inf_comm]; exact GreenBook.LieModels.ReeFour.overlap m)
    P Q M₁ M₂ D C hPM hQM hD₁ hD₂ hCD hPD hQD hprod₁ hprod₂
    eP eQ eC hPC hQC σ hσ hs hi ha hcP hcQ

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
