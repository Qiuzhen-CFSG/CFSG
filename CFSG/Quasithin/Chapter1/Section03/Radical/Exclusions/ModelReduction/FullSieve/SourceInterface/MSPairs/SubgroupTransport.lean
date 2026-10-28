module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs
public import Theory.Frattini.Intersection

/-!
# Inclusion transport for the literal MS sections

An injective group map transports the center, Frattini subgroup and commutator
core to their actual images. The section transport uses the induced quotient
isomorphism and proves the conjugation equation on representatives. Its relative
subgroup form applies to the inclusion of L ∨ R in the original ambient group.

This does not transport centrality under a larger group: the acting subgroup
is always the image of the specified actor. The distance-four SmallMSPair
consumer uses it for both sections with the same component marking.

Source: Aschbacher–Smith C.1.34, printed pp.136–137.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G H : Type*} [Group G] [Group H]

theorem centerIn_map (D : Subgroup G) (f : G →* H) (hf : Function.Injective f) :
    centerIn (D.map f) = (centerIn D).map f := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, hxy⟩ := z.property
    refine ⟨x, ?_, hxy⟩
    refine ⟨⟨x, hx⟩, mem_center_iff.mpr ?_, rfl⟩
    intro d
    apply Subtype.ext
    apply hf
    have he := congrArg Subtype.val
      (mem_center_iff.mp hz ((D.equivMapOfInjective f hf) d))
    change f (d : G) * (z : H) = (z : H) * f (d : G) at he
    change f ((d : G) * x) = f (x * (d : G))
    simpa only [map_mul, hxy] using he
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(D.equivMapOfInjective f hf) z, mem_center_iff.mpr ?_, rfl⟩
    intro y
    obtain ⟨w, rfl⟩ := (D.equivMapOfInjective f hf).surjective y
    simpa only [map_mul] using
      congrArg (D.equivMapOfInjective f hf) (mem_center_iff.mp hz w)

theorem frattiniIn_map (D : Subgroup G) (f : G →* H) (hf : Function.Injective f) :
    frattiniIn (D.map f) = (frattiniIn D).map f :=
  frattini_image_map D f hf

theorem HasSectionModel.map {B V F : Type*} [Group B] [AddCommGroup V]
    [Field F] [Module F V] {A D E : Subgroup G} {a : A →* B}
    {rho : Representation F B V} (h : HasSectionModel A D E a rho)
    (f : G →* H) (hf : Function.Injective f) (a' : A.map f →* B)
    (ha : ∀ x, a' ((A.equivMapOfInjective f hf) x) = a x) :
    HasSectionModel (A.map f) (D.map f) (E.map f) a' rho := by
  obtain ⟨hED, hAD, hAE, hn, e, he⟩ := h
  let := hn
  let d := D.equivMapOfInjective f hf
  have hED' : (E.subgroupOf D).map d.toMonoidHom =
      (E.map f).subgroupOf (D.map f) := by
    apply map_injective (D.map f).subtype_injective
    rw [map_subgroupOf_eq_of_le (map_mono hED), map_map]
    change (E.subgroupOf D).map (f.comp D.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hED]
  let hn' : ((E.map f).subgroupOf (D.map f)).Normal := by
    rw [← hED']
    exact Subgroup.Normal.map hn d.toMonoidHom d.surjective
  let := hn'
  let q := QuotientGroup.congr (E.subgroupOf D)
    ((E.map f).subgroupOf (D.map f)) d hED'
  refine ⟨map_mono hED, ?_, ?_, hn', q.symm.trans e, ?_⟩
  · exact (map_mono hAD).trans (D.le_normalizer_map f)
  · exact (map_mono hAE).trans (E.le_normalizer_map f)
  · intro l x y hy
    obtain ⟨l, rfl⟩ := (A.equivMapOfInjective f hf).surjective l
    obtain ⟨x, rfl⟩ := d.surjective x
    obtain ⟨y, rfl⟩ := d.surjective y
    have hxy : (y : G) = l * (x : G) * (l : G)⁻¹ := by
      apply hf
      change f (y : G) = f (l : G) * f (x : G) * (f (l : G))⁻¹ at hy
      simpa only [map_mul, map_inv] using hy
    have hq (x : D) : q.symm (QuotientGroup.mk' _ (d x)) =
        QuotientGroup.mk' _ x := by
      apply q.injective
      rw [q.apply_symm_apply]
      rfl
    simpa only [MulEquiv.trans_apply, hq, ha] using he l x y hxy
theorem HasSectionModel.of_subgroupOf {B V F : Type*} [Group B] [AddCommGroup V]
    [Field F] [Module F V] {J A D E : Subgroup G} (hA : A ≤ J) (hD : D ≤ J)
    (hE : E ≤ J) (a : A →* B) (rho : Representation F B V)
    (h : HasSectionModel (A.subgroupOf J) (D.subgroupOf J) (E.subgroupOf J)
      (a.comp (subgroupOfEquivOfLe hA).toMonoidHom) rho) :
    HasSectionModel A D E a rho := by
  let fA := MulEquiv.subgroupCongr (map_subgroupOf_eq_of_le hA)
  have h' := h.map J.subtype J.subtype_injective (a.comp fA.toMonoidHom)
    (fun _ => rfl)
  dsimp only [fA] at h'
  simp only [map_subgroupOf_eq_of_le hD, map_subgroupOf_eq_of_le hE] at h'
  have descend : ∀ (A' : Subgroup G) (heq : A' = A),
      HasSectionModel A' D E (a.comp (MulEquiv.subgroupCongr heq).toMonoidHom) rho →
        HasSectionModel A D E a rho := by
    intro A' heq
    subst A'
    exact fun hh => hh
  exact descend _ _ h'

theorem centerIn_subgroupOf {J D : Subgroup G} (hD : D ≤ J) :
    centerIn (D.subgroupOf J) = (centerIn D).subgroupOf J := by
  apply map_injective J.subtype_injective
  rw [← centerIn_map _ _ J.subtype_injective,
    map_subgroupOf_eq_of_le hD,
    map_subgroupOf_eq_of_le (show centerIn D ≤ J from
      (map_subtype_le (center D)).trans hD)]

theorem frattiniIn_subgroupOf {J D : Subgroup G} (hD : D ≤ J) :
    frattiniIn (D.subgroupOf J) = (frattiniIn D).subgroupOf J := by
  apply map_injective J.subtype_injective
  rw [← frattiniIn_map _ _ J.subtype_injective,
    map_subgroupOf_eq_of_le hD,
    map_subgroupOf_eq_of_le (show frattiniIn D ≤ J from
      (map_subtype_le (frattini D)).trans hD)]

theorem msQ_map (L R : Subgroup G) (f : G →* H) (hf : Function.Injective f) :
    msQ (L.map f) (R.map f) = (msQ L R).map f := by
  rw [msQ, msQ, map_commutator, map_pCoreIn_of_injective 2 _ _ hf, Subgroup.map_sup]

theorem msQ_le_join (L R : Subgroup G) : msQ L R ≤ L ⊔ R :=
  (@Subgroup.commutator_le_sup G _ ((L ⊔ R).pCoreIn 2) L).trans
    (sup_le (map_subtype_le _) le_sup_left)

theorem msQ_subgroupOf {J L R : Subgroup G} (hL : L ≤ J) (hR : R ≤ J) :
    msQ (L.subgroupOf J) (R.subgroupOf J) = (msQ L R).subgroupOf J := by
  apply map_injective J.subtype_injective
  rw [← msQ_map _ _ _ J.subtype_injective, map_subgroupOf_eq_of_le hL,
    map_subgroupOf_eq_of_le hR,
    map_subgroupOf_eq_of_le ((msQ_le_join L R).trans (sup_le hL hR))]

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
