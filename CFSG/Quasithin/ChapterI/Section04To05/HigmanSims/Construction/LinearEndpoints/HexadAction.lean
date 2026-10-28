module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadOvergroup
public import Theory.GroupTheory.NormalCoreTwoClosedTransport
public import Theory.GroupAction.SimpleCosets
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# Actual six-coset and twenty-one-radical actions

The original endpoint has index six in its literal alternating-six preimage.
Its coset action has precisely the original elementary radical as kernel.
The marked linear group has twenty-one literal conjugates of that radical.
The six-coset action is not identified with the retained polar six letters.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F
local notation "A6" => alternatingGroup (Fin 6)

private theorem radical_card (d : NaturalEndpointData A) : Nat.card A = 16 := by
  rw [Nat.card_congr d.coordinates.toEquiv]
  exact (Nat.card_eq_fintype_card (α := Representation.SL2FourNatural.V)).trans
    Representation.SL2FourNatural.card_vector

/-- The literal endpoint has six cosets in the original alternating-six preimage. -/
theorem NaturalEndpointData.hexad_endpoint_index (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier ≤ L) (e : L ≃* Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom = Point) :
    d.carrier.relIndex d.hexad_overgroup = 6 := by
  obtain ⟨_,_,hPD,hDcard,_⟩ := d.hexad_overgroup_structure L hPL e hmark
  have hh := (d.carrier.subgroupOf d.hexad_overgroup).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hPD).toEquiv,d.carrier_card,hDcard] at hh
  change (d.carrier.subgroupOf d.hexad_overgroup).index = 6
  omega

/-- The kernel of the actual six-coset action is exactly the original A. -/
theorem NaturalEndpointData.hexad_endpoint_coset_kernel (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier ≤ L) (e : L ≃* Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom = Point) :
    (MulAction.toPermHom d.hexad_overgroup
      (d.hexad_overgroup ⧸ d.carrier.subgroupOf d.hexad_overgroup)).ker =
      A.subgroupOf d.hexad_overgroup := by
  obtain ⟨_,_,_,_,_,π,hπs,hπker,_⟩ := d.hexad_overgroup_structure L hPL e hmark
  let P := d.carrier.subgroupOf d.hexad_overgroup
  let T := P.map π
  have hkP : π.ker ≤ P := hπker ▸ fun _ hx => d.kernel_le hx
  have hPT : T.comap π = P := comap_map_eq_self hkP
  have hi : T.index = 6 := by
    have hh := T.index_comap_of_surjective hπs
    rw [hPT] at hh
    exact hh.symm.trans (d.hexad_endpoint_index L hPL e hmark)
  have hT : T ≠ ⊤ := by
    intro he
    rw [he,index_top] at hi
    contradiction
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  rw [← normalCore_eq_ker]
  change P.normalCore = _
  rw [← hPT,normalCore_comap_of_surjective π hπs,
    T.normalCore_eq_bot_of_simple hT,MonoidHom.comap_bot,hπker]

/-- The original endpoint is not normal in its alternating-six overgroup. -/
theorem NaturalEndpointData.hexad_endpoint_not_normal (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier ≤ L) (e : L ≃* Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom = Point) :
    ¬ (d.carrier.subgroupOf d.hexad_overgroup).Normal := by
  obtain ⟨_,hAD,hPD,_⟩ := d.hexad_overgroup_structure L hPL e hmark
  intro hn
  let := hn
  have hh := d.hexad_endpoint_coset_kernel L hPL e hmark
  rw [← normalCore_eq_ker,normalCore_eq_self] at hh
  have hc := congrArg (fun S : Subgroup d.hexad_overgroup => Nat.card S) hh
  rw [Nat.card_congr (subgroupOfEquivOfLe hPD).toEquiv,d.carrier_card,
    Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv,radical_card d] at hc
  contradiction

/-- The twenty-one endpoint cosets are the twenty-one literal conjugates
of A in the original marked linear group. -/
theorem NaturalEndpointData.linear_three_radical_orbit (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier ≤ L) (e : L ≃* Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom = Point) :
    d.carrier.relIndex L = 21 ∧
      (Set.range fun g : L => A.map (MulAut.conj (g : G)).toMonoidHom).ncard = 21 := by
  have hcL : Nat.card L = 20160 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL
  have hi : d.carrier.relIndex L = 21 := by
    have hh := (d.carrier.subgroupOf L).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv,d.carrier_card,hcL] at hh
    change (d.carrier.subgroupOf L).index = 21
    omega
  refine ⟨hi,?_⟩
  let : MulAction L (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp L.subtype)
  have hs : MulAction.stabilizer L A = d.carrier.subgroupOf L := by
    ext g
    change A.map (MulAut.conj (g : G)).toMonoidHom = A ↔ (g : G) ∈ d.carrier
    have hh : A.map (MulAut.conj (g : G)).toMonoidHom = A ↔
        (g : G) ∈ normalizer (A : Set G) := mem_normalizer_iff_map_conj_eq.symm
    refine hh.trans ?_
    exact ⟨fun hg => (d.linear_three_radical_normalizer L hPL e hmark) ▸ ⟨g.property,hg⟩,
      fun hg => d.normalizes hg⟩
  have hh := Nat.card_congr (MulAction.orbitEquivQuotientStabilizer L A)
  rw [← index_eq_card,hs] at hh
  change (MulAction.orbit L A).ncard = 21
  exact hh.trans hi

end CFSG.Quasithin.HigmanSims
