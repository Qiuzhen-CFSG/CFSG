module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ActionKernel
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.LocalStructure
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer
public import Theory.Representation.BinaryOffender.CentralKernelPointResidual
public import Theory.SpecificGroups.Alternating.SevenComponent.PointSix
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# The actual nonsingular A₆ residual and its canonical containment

The original action map sends O²(C_L(v)) onto the pointwise fixer of the
two-point representative of v in V/C_V(L). Central-kernel lifting gives
this assertion even before the full module cover has been recognized.
Its kernel is O₂(L_v), so restriction to the six complementary letters
constructs the actual A₆ marking, commuting with the original projection.

Two-perfectness then makes L_v perfect. Since its simple quotient has
order divisible by three, L_v is its own prime-to-three residual.
Embedding this perfect subgroup in G_v^∞ gives L_v ≤ O^{3′}(G_v^∞)=K_v.
This proves the containment needed by local normalization without assuming
component recognition. It does not yet identify K_v as a C-component.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the opening
of Theorem 12.6.2 and the containment clause of Lemma 12.6.3, pp.823–824.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BinaryNaturalDual.VectorStabilizers
open scoped IsMulCommutative
open BinaryPermutation.EightNonsingular
namespace CFSG.Quasithin.Chapter12.Section06
universe u
variable {G : Type u} [Group G] [Finite G]

noncomputable def OrthogonalMarking.actorMap {L V : Subgroup G} [IsElementaryAbelian 2 V]
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn) :
    L →* alternatingGroup (Fin 8) :=
  D.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (conjugation L V hn).ker)

omit [Finite G] in
theorem OrthogonalMarking.actorMap_surjective {L V : Subgroup G} [IsElementaryAbelian 2 V]
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn) :
    Function.Surjective D.actorMap :=
  D.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

theorem OrthogonalMarking.actorMap_ker {T : Sylow 2 G} {L V : Subgroup G}
    [IsElementaryAbelian 2 V] (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hq : IsQuasisimple (Star L)) :
    D.actorMap.ker = pCore 2 L := by
  rw [actorMap, MonoidHom.ker_comp_of_injective _ _ D.groupEquiv.injective,
    QuotientGroup.ker_mk', D.actionKernel_eq_core chosen hq]

theorem OrthogonalMarking.Lv_image_pair {L V : Subgroup G} [IsElementaryAbelian 2 V]
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn)
    (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : BinaryPermutation.coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) :
    ((Lv L (v : G)).subgroupOf L).map D.actorMap = pointFixer i j := by
  let ρ := seedRepresentation L V hn
  let f := D.coordinates.toLinearMap.comp (fixedSeed L V hn).toSubmodule.mkQ
  have hf : ∀ g w, f (ρ g w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (D.actorMap g) (f w) :=
    fun g w => D.equivariant g (Submodule.Quotient.mk w)
  have hk : f.ker ≤ ρ.invariants := by
    intro w hw
    have hz : (fixedSeed L V hn).toSubmodule.mkQ w = 0 :=
      D.coordinates.injective (show D.coordinates _ = D.coordinates 0 from
        hw.trans D.coordinates.map_zero.symm)
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  let C := representationStabilizer ρ (Additive.ofMul v)
  have hC : C.map L.subtype = CLv L (v : G) := by
    ext x
    constructor
    · rintro ⟨l,hl,rfl⟩
      refine ⟨l.property, ?_⟩
      change (l : G) ∈ centralizer ({(v : G)} : Set G)
      rw [mem_centralizer_singleton_iff]
      have he := congrArg (fun w : Additive V => (w.toMul : G)) hl
      change (l : G) * (v : G) * (l : G)⁻¹ = v at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · rintro ⟨hl,hv⟩
      refine ⟨⟨x,hl⟩, ?_, rfl⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      change x * (v : G) * x⁻¹ = v
      change x ∈ centralizer ({(v : G)} : Set G) at hv
      rw [mem_centralizer_singleton_iff] at hv
      rw [hv, mul_inv_cancel_right]
  have hE : (pResidual 2 C).map C.subtype = (Lv L (v : G)).subgroupOf L := by
    have hh := map_embedded_pResidual 2 C L.subtype
    rw [hC] at hh
    apply (map_injective L.subtype_injective)
    rw [map_subgroupOf_eq_of_le (Lv_le_L L (v : G))]
    exact hh
  have hh := Representation.BinaryOffender.map_stabilizer_residual_of_central_kernel
    ρ (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) D.actorMap
    D.actorMap_surjective f hf hk (Additive.ofMul v)
  rw [hE] at hh
  change ((Lv L (v : G)).subgroupOf L).map D.actorMap =
    (pResidual 2 (stabilizer (D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))))).map
      (stabilizer (D.coordinates (Submodule.Quotient.mk (Additive.ofMul v)))).subtype at hh
  rw [← hp, stabilizer_residual i j hij] at hh
  exact hh


noncomputable def OrthogonalMarking.localPairMap {L V : Subgroup G}
    [IsElementaryAbelian 2 V] {hn : L ≤ normalizer (V : Set G)}
    (D : OrthogonalMarking L V hn) (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : BinaryPermutation.coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) :
    Lv L (v : G) →* pointFixer i j :=
  (D.actorMap.comp (inclusion (Lv_le_L L (v : G)))).codRestrict _ (fun x => by
    rw [← D.Lv_image_pair v i j hij hp]
    exact ⟨⟨x.val, Lv_le_L L (v : G) x.property⟩, x.property, rfl⟩)

theorem OrthogonalMarking.localPairMap_surjective {L V : Subgroup G}
    [IsElementaryAbelian 2 V] {hn : L ≤ normalizer (V : Set G)}
    (D : OrthogonalMarking L V hn) (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : BinaryPermutation.coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) :
    Function.Surjective (D.localPairMap v i j hij hp) := by
  intro a
  have ha := (D.Lv_image_pair v i j hij hp).ge a.property
  obtain ⟨l,hl,he⟩ := ha
  exact ⟨⟨l.val,hl⟩, Subtype.ext he⟩

noncomputable def OrthogonalMarking.localSixMap {L V : Subgroup G}
    [IsElementaryAbelian 2 V] {hn : L ≤ normalizer (V : Set G)}
    (D : OrthogonalMarking L V hn) (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : BinaryPermutation.coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) :
    Lv L (v : G) →* alternatingGroup (Fin 6) :=
  (pointFixerEquiv i j hij).toMonoidHom.comp (D.localPairMap v i j hij hp)

theorem OrthogonalMarking.localSixMap_surjective {L V : Subgroup G}
    [IsElementaryAbelian 2 V] {hn : L ≤ normalizer (V : Set G)}
    (D : OrthogonalMarking L V hn) (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : BinaryPermutation.coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) :
    Function.Surjective (D.localSixMap v i j hij hp) :=
  (pointFixerEquiv i j hij).surjective.comp (D.localPairMap_surjective v i j hij hp)

theorem OrthogonalMarking.localSixMap_ker {T : Sylow 2 G} {L V : Subgroup G}
    [IsElementaryAbelian 2 V] (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hq : IsQuasisimple (Star L))
    (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : BinaryPermutation.coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) :
    (D.localSixMap v i j hij hp).ker = pCore 2 (Lv L (v : G)) := by
  have he : (D.localSixMap v i j hij hp).ker =
      D.actorMap.ker.comap (inclusion (Lv_le_L L (v : G))) := by
    rw [localSixMap, MonoidHom.ker_comp_of_injective _ _ (pointFixerEquiv i j hij).injective,
      localPairMap, MonoidHom.ker_codRestrict]
    rfl
  have hk : IsPGroup 2 (D.localSixMap v i j hij hp).ker := by
    rw [he, D.actorMap_ker chosen hq]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective (Lv_le_L L (v : G)))
  have hh := (D.localSixMap v i j hij hp).comap_pCore_of_ker_isPGroup
    (D.localSixMap_surjective v i j hij hp) hk
  rwa [alternatingGroup.SevenComponent.alternating_six_twoCore, MonoidHom.comap_bot] at hh

noncomputable def OrthogonalMarking.localCoreQuotientEquiv
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hq : IsQuasisimple (Star L))
    (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : BinaryPermutation.coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) :
    Star (Lv L (v : G)) ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq (D.localSixMap_ker chosen hq v i j hij hp).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (D.localSixMap_surjective v i j hij hp))

theorem OrthogonalMarking.localCoreQuotientEquiv_mk
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hq : IsQuasisimple (Star L))
    (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : BinaryPermutation.coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v)))
    (l : Lv L (v : G)) :
    D.localCoreQuotientEquiv chosen hq v i j hij hp
      (QuotientGroup.mk' (pCore 2 (Lv L (v : G))) l) =
        pointFixerEquiv i j hij (D.localPairMap v i j hij hp l) := by rfl

theorem OrthogonalMarking.nonsingular_local_quotient
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hq : IsQuasisimple (Star L))
    (v : V) (hv : D.Nonsingular v) :
    Nonempty (Star (Lv L (v : G)) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  exact ⟨D.localCoreQuotientEquiv chosen hq v i j hij hp⟩

theorem Lv_le_Kv_of_A6 (L : Subgroup G) (v : G)
    (e : Star (Lv L v) ≃* alternatingGroup (Fin 6)) : Lv L v ≤ Kv v := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (Star (Lv L v)) := e.isSimpleGroup
  have hd : 3 ∣ Nat.card (Star (Lv L v)) := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hgen := primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 (Lv L v))
    pCore_isPGroup (isPPerfect_embedded_pResidual 2 (CLv L v)) hd
  let : Group.IsPerfect (Lv L v) := Lv_isPerfect_of_A6 L v e
  have hR := le_map_solvableResidual_of_isPerfect (Lv L v) (Gv v) (Lv_le_Gv L v)
  have hh := embedded_primeToResidual_mono 3 hR
  rw [hgen, ← MonoidHom.range_eq_map, range_subtype] at hh
  have he := map_embedded_primeToResidual_of_hom 3 (solvableResidual (Gv v)) (Gv v).subtype
  exact hh.trans_eq he.symm

theorem OrthogonalMarking.nonsingular_local_structure
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hq : IsQuasisimple (Star L))
    (v : V) (hv : D.Nonsingular v) :
    Nonempty (Star (Lv L (v : G)) ≃* alternatingGroup (Fin 6)) ∧
      Group.IsPerfect (Lv L (v : G)) ∧
      Lv L (v : G) = LvInfinity L (v : G) ∧ Lv L (v : G) ≤ Kv (v : G) := by
  obtain ⟨e⟩ := D.nonsingular_local_quotient chosen hq v hv
  exact ⟨⟨e⟩, Lv_isPerfect_of_A6 L (v : G) e,
    Lv_eq_LvInfinity_of_A6 L (v : G) e, Lv_le_Kv_of_A6 L (v : G) e⟩
end CFSG.Quasithin.Chapter12.Section06
