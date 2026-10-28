module
public import CFSG.Quasithin.Chapter5.Section03TrialitySource.NativeLift
public import Theory.GroupTheory.Amalgam.NormalBaseRecognition
public import CFSG.Quasithin.Chapter5.Section03GreenExtension

/-!
# Extending the native middle lift across both full normalizers

A pure parabolic is normal in its full endpoint because the endpoint is its
product with the common normalizer, whose native action preserves the pure
parabolic. Normal-supplement gluing extends the inner parabolic map and the
faithful native middle lift. Their exact inner preimages give injectivity.

The two endpoint maps agree on the entire common normalizer. Their native
ranges have precisely the arms and central inner intersections and the whole
middle as their intersection. Their join is an actual type-preserving
extension with inner-times-middle factorization. Both pure endpoint markings
and the common-normalizer map survive the construction.

Source: the realization step of Aschbacher–Smith 5.3.2, printed p.659, and
Definition F.4.3, p.274 of `refs/quasithin.pdf`. The native middle lift and the
source local products are supplied separately by the prepared-row application.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter5.Section03TrialitySource
open ChapterF.SourceCompletion.TrialityNonbinary
open ChapterF.SourceCompletion.UnitaryNonbinary (inner)
variable {G : Type*} [Group G] {m : ℕ} {hm : 0 < m}

private theorem glue_endpoint {U : Type*} [Group U]
    (hconj : Function.Injective (MulAut.conj : U →* MulAut U)) (P M D : Subgroup G)
    (hPM : P ≤ M) (hDM : D ≤ M) (hn : M ≤ normalizer (P : Set G))
    (hg : M = P ⊔ D)
    (R : Subgroup U) (e : P ≃* R)
    (ρ : D →* MulAut U)
    (hi : ∀ d : D, ρ d ∈ R.map MulAut.conj ↔ d.val ∈ P)
    (ha : ∀ (d : D) (hd : d.val ∈ P), MulAut.conj (e ⟨d.val,hd⟩).val = ρ d)
    (hc : ∀ (d : D) (x : P), ∃ hx : d.val*x.val*d.val⁻¹ ∈ P,
      (e ⟨d.val*x.val*d.val⁻¹,hx⟩).val = ρ d (e x).val) :
    ∃ f : M →* MulAut U, Function.Injective f ∧
      (∀ x : P, f (inclusion hPM x) = MulAut.conj (e x).val) ∧
      (∀ d : D, f (inclusion hDM d) = ρ d) ∧
      f.range = R.map MulAut.conj ⊔ ρ.range := by
  let N := P.subgroupOf M
  let T := D.subgroupOf M
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hPM).mpr hn
  let z : N ≃* R.map (MulAut.conj : U →* MulAut U) :=
    (subgroupOfEquivOfLe hPM).trans
      (e.trans (R.equivMapOfInjective MulAut.conj hconj))
  let v : T →* MulAut U := ρ.comp (subgroupOfEquivOfLe hDM).toMonoidHom
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


private theorem normalized_of_action {U : Type*} [Group U] (P D : Subgroup G)
    (R : Subgroup U) (e : P ≃* R) (ρ : D →* MulAut U)
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

private theorem endpoint_of_lift {U : Type*} [Group U]
    (hconj : Function.Injective (MulAut.conj : U →* MulAut U)) (P M D C : Subgroup G)
    (hPM : P ≤ M) (hDM : D ≤ M) (hPD : P ⊓ D = C)
    (hprod : ∀ x ∈ M, ∃ p ∈ P, ∃ d ∈ D, x = p*d)
    (R : Subgroup U) (e : P ≃* R) (ρ : D →* MulAut U)
    (hi : ∀ d : D, ρ d ∈ inner U ↔ d.val ∈ C)
    (ha : ∀ (d : D) (hd : d.val ∈ C), MulAut.conj (e ⟨d.val,(hPD.ge hd).1⟩).val = ρ d)
    (hc : ∀ (d : D) (x : P), ∃ hx : d.val*x.val*d.val⁻¹ ∈ P,
      (e ⟨d.val*x.val*d.val⁻¹,hx⟩).val = ρ d (e x).val) :
    ∃ f : M →* MulAut U, Function.Injective f ∧
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

/-- A faithful native middle lift extends across both full endpoints. The
whole common intersection and both pure markings are retained. -/
theorem extension_of_native_lift (P Q M₁ M₂ D C : Subgroup G)
    (hPM : P ≤ M₁) (hQM : Q ≤ M₂) (hD₁ : D ≤ M₁) (hD₂ : D ≤ M₂)
    (hCD : C ≤ D) (hPD : P ⊓ D = C) (hQD : Q ⊓ D = C)
    (hprod₁ : ∀ x ∈ M₁, ∃ p ∈ P, ∃ d ∈ D, x = p*d)
    (hprod₂ : ∀ x ∈ M₂, ∃ q ∈ Q, ∃ d ∈ D, x = q*d)
    (eP : P ≃* (parabolic (binaryParameters m hm) .arms))
    (eQ : Q ≃* (parabolic (binaryParameters m hm) .central)) (eC : C ≃* borel (binaryParameters m hm))
    (hPC : ∀ c : C, (eP ⟨c.val,(hPD.ge c.property).1⟩).val = (eC c).val)
    (hQC : ∀ c : C, (eQ ⟨c.val,(hQD.ge c.property).1⟩).val = (eC c).val)
    (σ : D →* flagAutomorphisms m hm) (hσ : Function.Injective σ)
    (hi : ∀ d : D, (σ d).val ∈ inner (BinaryCarrier m hm) ↔ d.val ∈ C)
    (ha : ∀ c : C, (σ (inclusion hCD c)).val = MulAut.conj (eC c).val)
    (hcP : ∀ (d : D) (x : P), ∃ hx : d.val*x.val*d.val⁻¹ ∈ P,
      (eP ⟨d.val*x.val*d.val⁻¹,hx⟩).val = (σ d).val (eP x).val)
    (hcQ : ∀ (d : D) (x : Q), ∃ hx : d.val*x.val*d.val⁻¹ ∈ Q,
      (eQ ⟨d.val*x.val*d.val⁻¹,hx⟩).val = (σ d).val (eQ x).val) :
    ∃ E : SourceExtension m hm,
      ∃ e : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups M₁ D M₂ hD₁ hD₂) E.amalgam,
        (∀ x : P, (e.left (inclusion hPM x)).val = MulAut.conj (eP x).val) ∧
        (∀ x : Q, (e.right (inclusion hQM x)).val = MulAut.conj (eQ x).val) ∧
        (∀ d : D, (e.middle d).val = (σ d).val) := by
  let ρ := (flagAutomorphisms m hm).subtype.comp σ
  obtain ⟨f,hf,hfP,hfD,hfr⟩ := endpoint_of_lift (conj_injective m hm) P M₁ D C hPM hD₁ hPD hprod₁
    (parabolic (binaryParameters m hm) .arms) eP ρ hi (by
      intro d hd
      rw [hPC ⟨d.val,hd⟩]
      exact (ha ⟨d.val,hd⟩).symm) hcP
  obtain ⟨g,hg,hgQ,hgD,hgr⟩ := endpoint_of_lift (conj_injective m hm) Q M₂ D C hQM hD₂ hQD hprod₂
    (parabolic (binaryParameters m hm) .central) eQ ρ hi (by
      intro d hd
      rw [hQC ⟨d.val,hd⟩]
      exact (ha ⟨d.val,hd⟩).symm) hcQ
  let α : Section03GreenExtension.LieAmalgam (BinaryCarrier m hm) :=
    ⟨parabolic (binaryParameters m hm) .arms, borel (binaryParameters m hm),
      parabolic (binaryParameters m hm) .central, borel_le_parabolic _ .arms,
      borel_le_parabolic _ .central, native_generate m hm⟩
  let γ : Section03GreenExtension.LocalAmalgam G := ⟨M₁,D,M₂,hD₁,hD₂⟩
  let a : Section03GreenExtension.CompatibleLocalActions α γ :=
    { left := f
      right := g
      middle := ρ
      left_injective := hf
      right_injective := hg
      middle_injective := Subtype.val_injective.comp hσ
      leftContains := by rw [hfr]; exact le_sup_left
      rightContains := by rw [hgr]; exact le_sup_left
      middle_left_range := by rw [hfr]; exact le_sup_right
      middle_right_range := by rw [hgr]; exact le_sup_right
      left_agrees := hfD
      right_agrees := hgD }
  have hmid : ρ.range ⊓ inner (BinaryCarrier m hm) = (borel (binaryParameters m hm)).map (MulAut.conj : BinaryCarrier m hm →* MulAut (BinaryCarrier m hm)) := by
    apply le_antisymm
    · rintro _ ⟨⟨d,rfl⟩,hd⟩
      have hb := (hi d).mp hd
      rw [show ρ d = MulAut.conj (eC ⟨d.val,hb⟩).val from ha ⟨d.val,hb⟩]
      exact ⟨_,(eC ⟨d.val,hb⟩).property,rfl⟩
    · rintro _ ⟨b,hb,rfl⟩
      refine ⟨⟨inclusion hCD (eC.symm ⟨b,hb⟩),?_⟩,⟨b,rfl⟩⟩
      change (σ (inclusion hCD _)).val = _
      rw [ha,eC.apply_symm_apply]
  have hp₁ (x : M₁) : ∃ p ∈ (parabolic (binaryParameters m hm) .arms), ∃ d : D,
      f x = MulAut.conj p * ρ d := by
    obtain ⟨p,hp,d,hd,he⟩ := hprod₁ x.val x.property
    refine ⟨(eP ⟨p,hp⟩).val,(eP ⟨p,hp⟩).property,⟨d,hd⟩,?_⟩
    have hx : x = inclusion hPM ⟨p,hp⟩ * inclusion hD₁ ⟨d,hd⟩ := Subtype.ext he
    rw [hx,map_mul,hfP,hfD]
  have hp₂ (x : M₂) : ∃ p ∈ (parabolic (binaryParameters m hm) .central), ∃ d : D,
      g x = MulAut.conj p * ρ d := by
    obtain ⟨p,hp,d,hd,he⟩ := hprod₂ x.val x.property
    refine ⟨(eQ ⟨p,hp⟩).val,(eQ ⟨p,hp⟩).property,⟨d,hd⟩,?_⟩
    have hx : x = inclusion hQM ⟨p,hp⟩ * inclusion hD₂ ⟨d,hd⟩ := Subtype.ext he
    rw [hx,map_mul,hgQ,hgD]
  obtain ⟨hl,hr,hinter⟩ := a.intersections (conj_injective m hm)
    (parabolic_inf_binary (binaryParameters m hm) rfl) hmid hp₁ hp₂
  let E : SourceExtension m hm :=
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
        exact ⟨x,ρ d,hinter.ge ⟨d,rfl⟩,rfl⟩
      preserves_types := by
        intro z hz
        obtain ⟨x,d,rfl⟩ := (a.completion_product hp₁ hp₂ z).mp hz
        constructor
        · refine ⟨x,?_⟩
          change (parabolic (binaryParameters m hm) .arms).map ((MulAut.conj x).toMonoidHom.comp (ρ d).toMonoidHom) = _
          rw [←Subgroup.map_map]
          exact congrArg (fun U => U.map (MulAut.conj x).toMonoidHom)
            (σ d).property.1
        · refine ⟨x,?_⟩
          change (parabolic (binaryParameters m hm) .central).map ((MulAut.conj x).toMonoidHom.comp (ρ d).toMonoidHom) = _
          rw [←Subgroup.map_map]
          exact congrArg (fun U => U.map (MulAut.conj x).toMonoidHom)
            (σ d).property.2 }
  let e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups M₁ D M₂ hD₁ hD₂) E.amalgam :=
    { left := MonoidHom.ofInjective hf
      right := MonoidHom.ofInjective hg
      middle := (MonoidHom.ofInjective (Subtype.val_injective.comp hσ)).trans
        (MulEquiv.subgroupCongr hinter.symm)
      left_commutes d := Subtype.ext (hfD d)
      right_commutes d := Subtype.ext (hgD d) }
  exact ⟨E,e,hfP,hgQ,fun _ => rfl⟩

end CFSG.Quasithin.Chapter5.Section03TrialitySource
