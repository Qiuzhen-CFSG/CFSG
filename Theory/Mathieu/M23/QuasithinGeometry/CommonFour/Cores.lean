module

public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Marking
public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow

/-!
# Intrinsic M23 cores and their common four-group

A normal two-subgroup of a local stabilizer lies in each of its Sylow
subgroups. The two checked Sylow intersections therefore bound the heptad
and quintet cores by the explicit E16 candidates. Conversely, the candidates
lie in the restrictions of the actual octad and sextet cores, hence in the
intrinsic local cores. Their intersection has order four; the exhaustive
Sylow E16 classification supplies global native conjugate coverage.

An ambient compatible Sylow group is constructed inside the intersection
of the octad and sextet stabilizers. Its preimage under the actual point
embedding is exactly the marked native M23 Sylow group.

Source: Aschbacher–Smith H.14.2(1), the order clause of H.14.1(6), and the
common subgroup in H.16.8, printed pp.396–397,405.
-/

@[expose] public section
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.CommonFour
open M24LocalGeometry MathieuCode FusionCertificate ElementarySylow

/-- Restricting an intrinsic core through a faithful homomorphism gives a normal
p-subgroup of the preimage stabilizer. Normality is relative to that stabilizer. -/
private theorem restricted_core_le {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (L : Subgroup H) :
    ((pCore 2 L).map L.subtype).comap f ≤
      (pCore 2 (L.comap f)).map (L.comap f).subtype := by
  let r : L.comap f →* L :=
    (f.comp (L.comap f).subtype).codRestrict _ (fun g => g.property)
  have hr : Function.Injective r := by
    intro a b h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  have hp : (pCore 2 L).comap r ≤ pCore 2 (L.comap f) :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective r hr⟩
  intro g hg
  obtain ⟨x,hx,hxe⟩ := hg
  have hgs : g ∈ L.comap f := by
    change f g ∈ L
    rw [← hxe]
    exact x.property
  refine ⟨⟨g,hgs⟩, hp ?_, rfl⟩
  change r ⟨g,hgs⟩ ∈ pCore 2 L
  have he : r ⟨g,hgs⟩ = x := Subtype.ext hxe.symm
  rwa [he]

private theorem core_le_candidate (b : Fin 2) :
    let H := if b = 0 then quintetStabilizer else markedHeptadStabilizer
    (pCore 2 H).map H.subtype ≤ standardCandidate b := by
  let H := if b = 0 then quintetStabilizer else markedHeptadStabilizer
  change (pCore 2 H).map H.subtype ≤ standardCandidate b
  have hSH : standardSylow.toSubgroup ≤ H := by
    fin_cases b
    · exact standardSylow_le_quintet
    · exact standardSylow_le_heptad
  have hp : pCore 2 H ≤ (standardSylow.subtype hSH).toSubgroup :=
    pCore_isPGroup.le_sylow_of_normal _
  rintro _ ⟨x,hx,rfl⟩
  apply sylow_intersection_le_candidate b x.val (hp hx)
  exact hp ((inferInstance : (pCore 2 H).Normal).conj_mem x hx ⟨move b,move_mem b⟩)

/-- The intrinsic quintet core is the marked native E16 candidate. -/
theorem quintet_core_eq :
    (pCore 2 quintetStabilizer).map quintetStabilizer.subtype = standardCandidate 0 := by
  apply le_antisymm (core_le_candidate 0)
  exact candidate0_le_sextetCore.trans
    (restricted_core_le pointEmbedding pointEmbedding_injective (sextetStabilizer standardSextet))

/-- The intrinsic heptad core is the marked native E16 candidate. -/
theorem heptad_core_eq :
    (pCore 2 markedHeptadStabilizer).map markedHeptadStabilizer.subtype = standardCandidate 1 := by
  apply le_antisymm (core_le_candidate 1)
  exact candidate1_le_octadCore.trans
    (restricted_core_le pointEmbedding pointEmbedding_injective (octadStabilizer standardOctad))

/-- Restricting the sextet core gives exactly the intrinsic quintet core. -/
theorem sextet_core_comap : SextetCore.core.comap pointEmbedding = standardCandidate 0 := by
  apply le_antisymm _ candidate0_le_sextetCore
  exact (restricted_core_le pointEmbedding pointEmbedding_injective
    (sextetStabilizer standardSextet)).trans (le_of_eq quintet_core_eq)

/-- Restricting the octad core gives exactly the intrinsic heptad core. -/
theorem octad_core_comap :
    ((pCore 2 (octadStabilizer standardOctad)).map
      (octadStabilizer standardOctad).subtype).comap pointEmbedding = standardCandidate 1 := by
  apply le_antisymm _ candidate1_le_octadCore
  exact (restricted_core_le pointEmbedding pointEmbedding_injective
    (octadStabilizer standardOctad)).trans (le_of_eq heptad_core_eq)

/-- The common subgroup is defined using the literal ambient octad and sextet cores. -/
noncomputable def commonKernel : Subgroup M23 :=
  (((pCore 2 (octadStabilizer standardOctad)).map (octadStabilizer standardOctad).subtype) ⊓
    SextetCore.core).comap pointEmbedding

/-- The finite common four-group is transported by an element of native M23. -/
theorem common_marking : common.map (MulAut.conj transport).toMonoidHom = commonKernel := by
  rw [commonKernel, Subgroup.comap_inf, octad_core_comap, sextet_core_comap,
    common, Subgroup.map_inf _ _ _ (MulAut.conj transport).injective]
  exact inf_comm _ _

theorem commonKernel_card : Nat.card commonKernel = 4 := by
  rw [← common_marking, Subgroup.card_map_of_injective (MulAut.conj transport).injective]
  exact common_card

/-- The whole ambient intersection fixes the distinguished point, so the
point embedding maps the native common group onto that intersection. -/
theorem commonKernel_map : commonKernel.map pointEmbedding =
    ((pCore 2 (octadStabilizer standardOctad)).map (octadStabilizer standardOctad).subtype) ⊓
      SextetCore.core := by
  apply Subgroup.map_comap_eq_self
  intro g hg
  rw [pointEmbedding_range]
  have ho : g ∈ octadPointwiseKernel standardOctad := by
    rw [← octad_core_map_eq_pointwise]
    exact hg.1
  exact (mem_octadPointwiseKernel standardOctad g).mp ho 0 (by decide +kernel)

/-- The ambient intersection of the actual octad and sextet cores has order four. -/
theorem ambient_common_card :
    Nat.card (((pCore 2 (octadStabilizer standardOctad)).map
      (octadStabilizer standardOctad).subtype) ⊓ SextetCore.core : Subgroup M24) = 4 := by
  rw [← commonKernel_map, Subgroup.card_map_of_injective pointEmbedding_injective,
    commonKernel_card]

/-- The two intrinsic cores are the only E16 subgroups in the compatible Sylow group. -/
theorem card16_eq_core (A : Subgroup M23) (hA : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 16) (hAS : A ≤ standardSylow.toSubgroup) :
    A = (pCore 2 quintetStabilizer).map quintetStabilizer.subtype ∨
      A = (pCore 2 markedHeptadStabilizer).map markedHeptadStabilizer.subtype := by
  let _ := hA
  let B := A.map (MulAut.conj transport⁻¹).toMonoidHom
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBc : Nat.card B = 16 :=
    (Subgroup.card_map_of_injective (MulAut.conj transport⁻¹).injective).trans hc
  have hBS : B ≤ subgroup := by
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨x,hx,hxa⟩ := hAS ha
    have he : (MulAut.conj transport⁻¹) a = x := by
      rw [← hxa]
      simp [MulAut.conj_apply, mul_assoc]
    exact he ▸ hx
  obtain ⟨b,hb⟩ := card16_eq_candidate B hB hBc hBS
  have he : A = standardCandidate b := by
    rw [standardCandidate, ← hb, Subgroup.map_map]
    have hh : (MulAut.conj transport).toMonoidHom.comp
        (MulAut.conj transport⁻¹).toMonoidHom = MonoidHom.id M23 := by
      ext a
      simp [MulAut.conj_apply, mul_assoc]
    rw [hh, Subgroup.map_id]
  rw [quintet_core_eq, heptad_core_eq]
  fin_cases b
  · exact Or.inl he
  · exact Or.inr he

/-- Both intrinsic cores belong to the same native Sylow subgroup; their
intersection is the common marked four-group. -/
theorem compatible_cores :
    (pCore 2 quintetStabilizer).map quintetStabilizer.subtype ≤ standardSylow.toSubgroup ∧
    (pCore 2 markedHeptadStabilizer).map markedHeptadStabilizer.subtype ≤ standardSylow.toSubgroup ∧
    commonKernel = ((pCore 2 quintetStabilizer).map quintetStabilizer.subtype) ⊓
      ((pCore 2 markedHeptadStabilizer).map markedHeptadStabilizer.subtype) := by
  rw [quintet_core_eq, heptad_core_eq]
  refine ⟨standardCandidate_le_sylow 0, standardCandidate_le_sylow 1, ?_⟩
  rw [commonKernel, Subgroup.comap_inf, octad_core_comap, sextet_core_comap, inf_comm]

/-- The two intrinsic cores are distinct, since their intersection has order four. -/
theorem cores_distinct :
    (pCore 2 quintetStabilizer).map quintetStabilizer.subtype ≠
      (pCore 2 markedHeptadStabilizer).map markedHeptadStabilizer.subtype := by
  intro h
  have hc := commonKernel_card
  rw [compatible_cores.2.2, h, inf_idem, heptad_core_eq, standardCandidate_card] at hc
  norm_num at hc

/-- The native M23 Sylow group is the restriction of an M24 Sylow group
stabilizing both marked objects, as in the source's choice of T₀ and T. -/
theorem exists_ambient_compatible_sylow : ∃ T₀ : Sylow 2 M24,
    T₀.toSubgroup ≤ octadStabilizer standardOctad ∧
    T₀.toSubgroup ≤ sextetStabilizer standardSextet ∧
    T₀.toSubgroup.comap pointEmbedding = standardSylow.toSubgroup := by
  let R := octadStabilizer standardOctad ⊓ sextetStabilizer standardSextet
  have h24R : SextetCore.standardSylow.toSubgroup ≤ R :=
    le_inf SextetCore.standardSylow_le_octadStabilizer SextetCore.standardSylow_le_stabilizer
  let A := standardSylow.toSubgroup.map pointEmbedding
  have hAR : A ≤ R := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨standardSylow_le_heptad hx,standardSylow_le_quintet hx⟩
  have hAp : IsPGroup 2 A := standardSylow.isPGroup'.map pointEmbedding
  obtain ⟨P,hAP⟩ := (hAp.comap_subtype (K := R)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq R (SextetCore.standardSylow.subtype h24R) P
  let T₀ : Sylow 2 M24 := g.val • SextetCore.standardSylow
  have hT₀R : T₀.toSubgroup ≤ R := Sylow.smul_le h24R g
  have he : T₀.subtype hT₀R = P := (Sylow.smul_subtype h24R g).symm.trans hg
  have hST : standardSylow.toSubgroup ≤ T₀.toSubgroup.comap pointEmbedding := by
    intro x hx
    have hA : pointEmbedding x ∈ A := ⟨x,hx,rfl⟩
    have hP : (⟨pointEmbedding x,hAR hA⟩ : R) ∈ P := hAP hA
    rw [← he] at hP
    exact hP
  refine ⟨T₀,hT₀R.trans inf_le_left,hT₀R.trans inf_le_right,?_⟩
  exact standardSylow.is_maximal'
    (T₀.isPGroup'.comap_of_injective pointEmbedding pointEmbedding_injective) hST

/-- Every elementary abelian subgroup of order sixteen contains a conjugate
of the literal marked intersection of octad and sextet cores. -/
theorem card16_contains_commonKernel_conjugate (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    ∃ g : M23, commonKernel.map (MulAut.conj g).toMonoidHom ≤ A := by
  obtain ⟨u,hu⟩ := card16_contains_common_conjugate A hA hc
  refine ⟨u * transport⁻¹, ?_⟩
  rw [← common_marking, Subgroup.map_map]
  have he : (MulAut.conj (u * transport⁻¹)).toMonoidHom.comp
      (MulAut.conj transport).toMonoidHom = (MulAut.conj u).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he]
  exact hu

end Sporadic.Mathieu.M23Geometry.CommonFour
