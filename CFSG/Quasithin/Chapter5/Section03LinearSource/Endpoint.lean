module
public import CFSG.Quasithin.Chapter5.Section03LinearSource.MarkedAction
public import CFSG.Quasithin.Chapter5.Section03GreenExtension
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Basic
public import Theory.GroupTheory.Amalgam.NormalBaseRecognition

/-!
# Compatible realization of the full linear endpoints

A faithful marked action of the common normalizer extends across each pure
parabolic by normal-supplement gluing. Its exact inner preimage ensures both
extensions are injective. The common action identifies their entire image
intersection; their join is an actual type-preserving automorphism extension.
The construction retains both pure endpoint markings and their common map.

The local gluing calculation is adapted from Section03SymplecticSource.Endpoint;
its argument is group-theoretic. Here the native group and endpoints are parameters,
and the prepared linear application supplies the model and every hypothesis.
Source: Aschbacher–Smith 5.3.2, printed p.659, and F.4.3, p.274
of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter5.Section03LinearSource
variable {G X : Type*} [Group G] [Group X]
variable (hinner : Function.Injective (MulAut.conj : X →* MulAut X))
include hinner
private theorem glue_endpoint (P M D : Subgroup G)
    (hPM : P ≤ M) (hDM : D ≤ M) (hn : M ≤ normalizer (P : Set G))
    (hg : M = P ⊔ D)
    (R : Subgroup X) (e : P ≃* R)
    (ρ : D →* MulAut X)
    (hi : ∀ d : D, ρ d ∈ R.map MulAut.conj ↔ d.val ∈ P)
    (ha : ∀ (d : D) (hd : d.val ∈ P), MulAut.conj (e ⟨d.val,hd⟩).val = ρ d)
    (hc : ∀ (d : D) (x : P), ∃ hx : d.val*x.val*d.val⁻¹ ∈ P,
      (e ⟨d.val*x.val*d.val⁻¹,hx⟩).val = ρ d (e x).val) :
    ∃ f : M →* MulAut X, Function.Injective f ∧
      (∀ x : P, f (inclusion hPM x) = MulAut.conj (e x).val) ∧
      (∀ d : D, f (inclusion hDM d) = ρ d) ∧
      f.range = R.map MulAut.conj ⊔ ρ.range := by
  let N := P.subgroupOf M
  let T := D.subgroupOf M
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hPM).mpr hn
  let z : N ≃* R.map (MulAut.conj : X →* MulAut X) :=
    (subgroupOfEquivOfLe hPM).trans
      (e.trans (R.equivMapOfInjective MulAut.conj hinner))
  let v : T →* MulAut X := ρ.comp (subgroupOfEquivOfLe hDM).toMonoidHom
  have hv : v.range = ρ.range := by
    ext a
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨subgroupOfEquivOfLe hDM t,rfl⟩
    · rintro ⟨d,rfl⟩
      exact ⟨(subgroupOfEquivOfLe hDM).symm d, rfl⟩
  have hgen : N ⊔ T = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hPM, map_subgroupOf_eq_of_le hDM,
      ←MonoidHom.range_eq_map, range_subtype, ←hg]
  obtain ⟨f,hf,hv'⟩ := RankTwoAmalgam.NormalBaseRecognition.exists_endpoint_equiv N T
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


omit hinner in
private theorem normalized_of_action (P D : Subgroup G)
    (R : Subgroup X) (e : P ≃* R) (ρ : D →* MulAut X)
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

private theorem endpoint_of_lift (P M D C : Subgroup G)
    (hPM : P ≤ M) (hDM : D ≤ M) (hPD : P ⊓ D = C)
    (hprod : ∀ x ∈ M, ∃ p ∈ P, ∃ d ∈ D, x = p*d)
    (R : Subgroup X) (e : P ≃* R) (ρ : D →* MulAut X)
    (hi : ∀ d : D, ρ d ∈ (MulAut.conj : X →* MulAut X).range ↔ d.val ∈ C)
    (ha : ∀ (d : D) (hd : d.val ∈ C), MulAut.conj (e ⟨d.val,(hPD.ge hd).1⟩).val = ρ d)
    (hc : ∀ (d : D) (x : P), ∃ hx : d.val*x.val*d.val⁻¹ ∈ P,
      (e ⟨d.val*x.val*d.val⁻¹,hx⟩).val = ρ d (e x).val) :
    ∃ f : M →* MulAut X, Function.Injective f ∧
      (∀ x : P, f (inclusion hPM x) = MulAut.conj (e x).val) ∧
      (∀ d : D, f (inclusion hDM d) = ρ d) ∧
      f.range = R.map MulAut.conj ⊔ ρ.range := by
  have hg : M = P ⊔ D := by
    apply le_antisymm _ (sup_le hPM hDM)
    intro x hx
    obtain ⟨p,hp,d,hd,rfl⟩ := hprod x hx
    exact Subgroup.mul_mem_sup hp hd
  apply glue_endpoint hinner P M D hPM hDM
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


/-- Reconstruct both full endpoints inside one actual automorphism extension. -/
theorem MarkedAction.extension
    {P Q D R U} (a : MarkedAction (G := G) (X := X) P Q D R U)
    (hgen : R ⊔ U = ⊤) (hself : normalizer ((R ⊓ U : Subgroup X) : Set X) = R ⊓ U)
    (M₁ M₂ : Subgroup G) (hPM : P ≤ M₁) (hQM : Q ≤ M₂)
    (hD₁ : D ≤ M₁) (hD₂ : D ≤ M₂)
    (hPD : P ⊓ D = P ⊓ Q) (hQD : Q ⊓ D = P ⊓ Q)
    (hprod₁ : ∀ x ∈ M₁, ∃ p ∈ P, ∃ d ∈ D, x = p*d)
    (hprod₂ : ∀ x ∈ M₂, ∃ q ∈ Q, ∃ d ∈ D, x = q*d) :
    ∃ E : ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension R U,
      ∃ e : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups M₁ D M₂ hD₁ hD₂) E.amalgam,
        (∀ x : P, (e.left (inclusion hPM x)).val = MulAut.conj (a.left x).val) ∧
        (∀ x : Q, (e.right (inclusion hQM x)).val = MulAut.conj (a.right x).val) ∧
        (∀ d : D, (e.middle d).val = a.action d) := by
  let ρ := a.action
  obtain ⟨f,hf,hfP,hfD,hfr⟩ := endpoint_of_lift hinner P M₁ D (P ⊓ Q) hPM hD₁ hPD hprod₁
    R a.left ρ (a.inner_iff hgen hself) (by
      intro d hd
      rw [show (a.left ⟨d.val,(hPD.ge hd).1⟩).val = (a.middle ⟨d.val,hd⟩).val from
        a.left_middle ⟨d.val,hd⟩]
      exact (a.inner_on_overlap hgen ⟨d.val,hd⟩).symm) a.left_action
  obtain ⟨g,hg,hgQ,hgD,hgr⟩ := endpoint_of_lift hinner Q M₂ D (P ⊓ Q) hQM hD₂ hQD hprod₂
    U a.right ρ (a.inner_iff hgen hself) (by
      intro d hd
      rw [show (a.right ⟨d.val,(hQD.ge hd).1⟩).val = (a.middle ⟨d.val,hd⟩).val from
        a.right_middle ⟨d.val,hd⟩]
      exact (a.inner_on_overlap hgen ⟨d.val,hd⟩).symm) a.right_action
  let α : Section03GreenExtension.LieAmalgam X :=
    ⟨R,R ⊓ U,U,inf_le_left,inf_le_right,hgen⟩
  let γ : Section03GreenExtension.LocalAmalgam G := ⟨M₁,D,M₂,hD₁,hD₂⟩
  let c : Section03GreenExtension.CompatibleLocalActions α γ :=
    { left := f
      right := g
      middle := ρ
      left_injective := hf
      right_injective := hg
      middle_injective := a.faithful
      leftContains := by rw [hfr]; exact le_sup_left
      rightContains := by rw [hgr]; exact le_sup_left
      middle_left_range := by rw [hfr]; exact le_sup_right
      middle_right_range := by rw [hgr]; exact le_sup_right
      left_agrees := hfD
      right_agrees := hgD }
  have hmid : ρ.range ⊓ (MulAut.conj : X →* MulAut X).range =
      (R ⊓ U).map (MulAut.conj : X →* MulAut X) := by
    apply le_antisymm
    · rintro _ ⟨⟨d,rfl⟩,hd⟩
      have hb := (a.inner_iff hgen hself d).mp hd
      rw [show ρ d = MulAut.conj (a.middle ⟨d.val,hb⟩).val from a.inner_on_overlap hgen ⟨d.val,hb⟩]
      exact ⟨_,(a.middle ⟨d.val,hb⟩).property,rfl⟩
    · rintro _ ⟨b,hb,rfl⟩
      refine ⟨⟨inclusion a.middle_le (a.middle.symm ⟨b,hb⟩),?_⟩,⟨b,rfl⟩⟩
      change a.action (inclusion a.middle_le _) = _
      rw [a.inner_on_overlap hgen,a.middle.apply_symm_apply]
  have hp₁ (x : M₁) : ∃ p ∈ R, ∃ d : D, f x = MulAut.conj p * ρ d := by
    obtain ⟨p,hp,d,hd,he⟩ := hprod₁ x.val x.property
    refine ⟨(a.left ⟨p,hp⟩).val,(a.left ⟨p,hp⟩).property,⟨d,hd⟩,?_⟩
    have hx : x = inclusion hPM ⟨p,hp⟩ * inclusion hD₁ ⟨d,hd⟩ := Subtype.ext he
    rw [hx,map_mul,hfP,hfD]
  have hp₂ (x : M₂) : ∃ p ∈ U, ∃ d : D, g x = MulAut.conj p * ρ d := by
    obtain ⟨p,hp,d,hd,he⟩ := hprod₂ x.val x.property
    refine ⟨(a.right ⟨p,hp⟩).val,(a.right ⟨p,hp⟩).property,⟨d,hd⟩,?_⟩
    have hx : x = inclusion hQM ⟨p,hp⟩ * inclusion hD₂ ⟨d,hd⟩ := Subtype.ext he
    rw [hx,map_mul,hgQ,hgD]
  obtain ⟨hl,hr,hm⟩ := c.intersections hinner rfl hmid hp₁ hp₂
  let E : ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension R U :=
    { carrier := c.completion
      left := f.range
      right := g.range
      left_le := le_sup_left
      right_le := le_sup_right
      contains_inner := c.inner_le_completion
      left_inner := hl
      right_inner := hr
      factor := by
        intro z hz
        obtain ⟨x,d,rfl⟩ := (c.completion_product hp₁ hp₂ z).mp hz
        exact ⟨x,ρ d,hm.ge ⟨d,rfl⟩,rfl⟩
      preserves_types := by
        intro z hz
        obtain ⟨x,d,rfl⟩ := (c.completion_product hp₁ hp₂ z).mp hz
        constructor
        · refine ⟨x,?_⟩
          change R.map ((MulAut.conj x).toMonoidHom.comp (ρ d).toMonoidHom) = _
          rw [←Subgroup.map_map]
          exact congrArg (fun V => V.map (MulAut.conj x).toMonoidHom) (a.preserves_left d)
        · refine ⟨x,?_⟩
          change U.map ((MulAut.conj x).toMonoidHom.comp (ρ d).toMonoidHom) = _
          rw [←Subgroup.map_map]
          exact congrArg (fun V => V.map (MulAut.conj x).toMonoidHom) (a.preserves_right d) }
  let e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups M₁ D M₂ hD₁ hD₂) E.amalgam :=
    { left := MonoidHom.ofInjective hf
      right := MonoidHom.ofInjective hg
      middle := (MonoidHom.ofInjective a.faithful).trans (MulEquiv.subgroupCongr hm.symm)
      left_commutes d := Subtype.ext (hfD d)
      right_commutes d := Subtype.ext (hgD d) }
  exact ⟨E,e,hfP,hgQ,fun _ => rfl⟩
end CFSG.Quasithin.Chapter5.Section03LinearSource
