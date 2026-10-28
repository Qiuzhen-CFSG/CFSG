module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceCrossing
public import Theory.GroupTheory.PGroup.DihedralSquareAutomorphisms
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FiveDihedralRecognition
public import Theory.Representation.BinaryPermutation.FivePairFaithful
/-!
# The original rank-one dihedral endgame

Generating elementary conjugate cores make C_S(L) central and identify S with
that elementary central factor times D8 times D8. The intrinsic automorphism
result then makes the two-residual of N_G(S) preserve Q=O2(LS). Uniqueness
over LT and the Sylow supplement put the full Baumann normalizer in N_G(L).
The generated cores are constructed by RankOneBaumannSourceGeneration.

Source: Aschbacher--Smith 5.1.7(1), pp.633--634.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Input
open ChapterB ChapterC
open ChapterC.Section05.CounterexampleCharacteristic
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W₀ : Subgroup G} {n : ℕ}
  (d : Input KnownSimple.IsKnownSimple T L W₀ n)
local notation "V" => (⁅W₀,L⁆ : Subgroup G)
include d
theorem baumann_normalizer_of_dihedral_square
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (e : baumann (T : Subgroup G) ≃* E × (DihedralGroup 4 × DihedralGroup 4)) :
    normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨_,hb,hV,_⟩ := alternating_block_of_baumann_escape d hout
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  let N := normalizer (S : Set G)
  have hTS : (T : Subgroup G) ≤ N :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hQS : Q ≤ S := baumann_core_le_of_escape d hout
  have hVQ : V ≤ Q := by
    change V ≤ (L ⊔ baumann (T : Subgroup G)).pCoreIn 2
    rw [baumann_core_product_of_escape d hout]
    exact le_sup_left
  have hnorm : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) := by
    apply (show L ⊔ (T : Subgroup G) ≤ normalizer ((L ⊔ S : Subgroup G) : Set G) from ?_).trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ S) (pCore 2 ↥(L ⊔ S)))
    apply sup_le ((show L ≤ L ⊔ S from le_sup_left).trans (L ⊔ S).le_normalizer)
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (d.sylow_normalizes ht),
      mem_normalizer_iff_map_conj_eq.mp (hTS ht)]
  have hNQ : normalizer (Q : Set G) ≤ normalizer (L : Set G) :=
    normalizer_of_local_normal d Q
      (fun h => d.noncentral (bot_unique (hVQ.trans_eq h)))
      (hQS.trans inf_le_left) (normal_subgroupOf_of_le_normalizer hnorm)
  have hZ : (center S).map S.subtype ≤ Q := by
    have he := ReducedMarking.normal_short_extension_centralizer L S hb.2.1
      (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left))
      (inf_le_left.trans d.sylow_normalizes)
    change (L ⊔ S) ⊓ centralizer ((blockU L).map L.subtype : Set G) = Q at he
    rw [hV] at he
    apply le_trans ?_ he.le
    refine le_inf ((map_subtype_le _).trans le_sup_right) ?_
    rintro _ ⟨z,hz,rfl⟩ v hv
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨v,hQS (hVQ hv)⟩)
  have hres : (pResidual 2 N).map N.subtype ≤ normalizer (L : Set G) :=
    (pResidual_normalizer_le_normalizer_of_dihedral_square S Q e hQS hZ).trans hNQ
  have hgen := congrArg (Subgroup.map N.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTS))
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTS,
    ←MonoidHom.range_eq_map,range_subtype] at hgen
  exact hout (hgen.symm.le.trans (sup_le hres d.sylow_normalizes))

theorem baumann_normalizer_of_generated_elementary_cores
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hQ : IsElementaryAbelian 2 ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2))
    (g : G) (hg : g ∈ normalizer (baumann (T : Subgroup G) : Set G))
    (hcross : baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom)
    (hgen : (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 ⊔
      ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom =
        baumann (T : Subgroup G))
    : False := by
  have hdis := baumann_core_disjoint_of_escape d hout
  have hker := baumann_core_centralizer_of_escape d hout
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  let C := S ⊓ centralizer (L : Set G)
  let W := Q.map (MulAut.conj g⁻¹).toMonoidHom
  change Q = S ⊓ centralizer (V : Set G) at hker
  let := hQ
  have hQC : Q = V ⊔ C := baumann_core_product_of_escape d hout
  have hQS : Q ≤ S := baumann_core_le_of_escape d hout
  have hVS : V ≤ S := (le_sup_left.trans hQC.ge).trans hQS
  have hCQ : C ≤ Q := le_sup_right.trans hQC.ge
  have hWS : W ≤ S := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hQS
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp ((normalizer (S:Set G)).inv_mem hg))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (W.subgroupOf S) := IsElementaryAbelian.subgroupOf hWS
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le hCQ
  let : IsElementaryAbelian 2 (C.subgroupOf S) := IsElementaryAbelian.subgroupOf inf_le_left
  have hCZ : C.subgroupOf S ≤ center S := by
    intro c hc
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    have hQcomm : Q ≤ centralizer ({(c:G)} : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : Q) ⟨c,hCQ hc⟩))
    have hWcomm : W ≤ centralizer ({(c:G)} : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : W) ⟨c,hcross hc⟩))
    exact mem_centralizer_singleton_iff.mp ((sup_le hQcomm hWcomm) (hgen.symm ▸ s.property))
  obtain ⟨q,m,hq,hm,hr,he,himage⟩ := exists_baumann_action_marking d hout
  have hSN : S ≤ L ⊔ (T : Subgroup G) := inf_le_left.trans le_sup_right
  let p := q.comp (inclusion hSN)
  have hp : p.range = Offenders.D 5 := by
    rw [←himage]
    ext x
    constructor
    · rintro ⟨s,rfl⟩; exact ⟨inclusion hSN s,s.property,rfl⟩
    · rintro ⟨s,hs,rfl⟩; exact ⟨⟨s,hs⟩,rfl⟩
  have hpk : p.ker = ((V).subgroupOf S) ⊔ (C.subgroupOf S) := by
    have hkerS : p.ker = (S ⊓ centralizer (V : Set G)).subgroupOf S := by
      ext s
      change p s = 1 ↔ (s:G) ∈ S ∧ (s:G) ∈ centralizer (V : Set G)
      constructor
      · intro hh
        refine ⟨s.property,?_⟩
        intro x hx
        obtain ⟨y,rfl⟩ := hr.symm ▸ hx
        have hv := he (inclusion hSN s) y.toAdd
        change _ = m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) y.toAdd)) at hv
        rw [hh,map_one] at hv
        exact (mul_inv_eq_iff_eq_mul.mp hv).symm
      · intro hh
        apply BinaryPermutation.FivePair.core_injective
        apply LinearMap.ext
        intro x
        apply Multiplicative.ofAdd.injective
        apply hm
        change m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) x)) = m (Multiplicative.ofAdd x)
        have heq := he (inclusion hSN s) x
        change _ = m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) x)) at heq
        rw [←heq]
        exact mul_inv_eq_iff_eq_mul.mpr (hh.2 _ (hr.le ⟨_,rfl⟩)).symm
    calc
      p.ker = (S ⊓ centralizer (V : Set G)).subgroupOf S := hkerS
      _ = Q.subgroupOf S := congrArg (fun H : Subgroup G => H.subgroupOf S) hker.symm
      _ = (V ⊔ C).subgroupOf S := congrArg (fun H : Subgroup G => H.subgroupOf S) hQC
      _ = (V).subgroupOf S ⊔ C.subgroupOf S := subgroupOf_sup hVS inf_le_left
  have hgen' : (V).subgroupOf S ⊔ C.subgroupOf S ⊔ W.subgroupOf S = ⊤ := by
    rw [←subgroupOf_sup hVS inf_le_left,←hQC,←subgroupOf_sup hQS hWS]
    exact hgen ▸ subgroupOf_self S
  let m0 : Multiplicative (BinaryPermutation.core (Fin 5)) →* (V).subgroupOf S := {
    toFun := fun x => ⟨⟨m x,hVS (hr.le ⟨x,rfl⟩)⟩,hr.le ⟨x,rfl⟩⟩
    map_one' := Subtype.ext (Subtype.ext (map_one m))
    map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul m x y)) }
  have hmi : Function.Injective m0 := fun x y hh => hm (congrArg (fun z : (V).subgroupOf S => ((z:S):G)) hh)
  have hms : Function.Surjective m0 := by
    intro v
    obtain ⟨x,hx⟩ := hr.ge v.property
    exact ⟨x,Subtype.ext (Subtype.ext hx)⟩
  let f := MulEquiv.ofBijective m0 ⟨hmi,hms⟩
  have hfe : ∀ (s:S) (x : BinaryPermutation.core (Fin 5)),
      (f (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) x)) : S) =
        s * (f (Multiplicative.ofAdd x) : S) * s⁻¹ := by
    intro s x
    apply Subtype.ext
    exact (he (inclusion hSN s) x).symm
  have hd : Disjoint ((V).subgroupOf S) (C.subgroupOf S) := by
    rw [disjoint_def]
    intro x hx hy
    exact Subtype.ext (disjoint_def.mp hdis hx hy)
  obtain ⟨e⟩ := Offenders.dihedral_square_of_core_action ((V).subgroupOf S) (C.subgroupOf S)
    (W.subgroupOf S) hCZ hd p hp hpk hgen' f hfe
  exact hout (baumann_normalizer_of_dihedral_square d e)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Input
