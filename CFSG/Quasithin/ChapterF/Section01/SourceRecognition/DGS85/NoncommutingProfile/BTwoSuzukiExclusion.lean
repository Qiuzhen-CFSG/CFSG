module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSuzukiSeed
public import Theory.SpecificGroups.Suzuki.SylowCommutator
public import Theory.SpecificGroups.Suzuki.SmallSylowFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSylowFrattini

/-!
# Excluding Suzuki beta quotients

The alpha core covers the beta quotient Sylow. The elementary seed image
lies in its omega subgroup, which is its derived subgroup in the nonbinary
Suzuki model. Lifting commutators therefore places the seed in the alpha
Frattini subgroup times the adjacent-core intersection. The proved source
Frattini obstruction excludes this possibility.

This closes the hypothetical nonbinary Suzuki branch analyzed in
BTwoSuzukiSeed. For Sz(2), the cyclic Sylow's involutions lie in its
Frattini subgroup, and the general Frattini lifting argument excludes
that parameter as well. The proof retains the actual beta quotient and only the
earlier center, (6.5), and (7.4) inputs. Other beta-model selection and
the remaining Chapter 10 conclusions are separate obligations.
Source: DGS, Groups and Graphs (1985), (10.7), printed pp.158--159;
Suzuki root derived structure: Huppert--Blackburn III, XI.3.1.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G]

private theorem elementary_image_of_section
    {H : Type*} [Group H] (J D L : Subgroup G) (hJL : J ≤ L)
    [(D.subgroupOf J).Normal] [IsElementaryAbelian 2 (J ⧸ D.subgroupOf J)]
    (q : L →* H) (hD : D.subgroupOf L ≤ q.ker) :
    IsElementaryAbelian 2 ((J.subgroupOf L).map q) := by
  let f : J →* (J.subgroupOf L).map q :=
    { toFun := fun x => ⟨q ⟨x,hJL x.property⟩,⟨⟨x,hJL x.property⟩,x.property,rfl⟩⟩
      map_one' := Subtype.ext q.map_one
      map_mul' := fun x y => Subtype.ext (q.map_mul (⟨x,hJL x.property⟩ : L) (⟨y,hJL y.property⟩ : L)) }
  have hker : D.subgroupOf J ≤ f.ker := by
    intro x hx
    exact Subtype.ext (hD hx)
  let f' := QuotientGroup.lift (D.subgroupOf J) f hker
  apply IsElementaryAbelian.of_surjective f'
  intro x
  obtain ⟨a,ha,he⟩ := x.property
  exact ⟨QuotientGroup.mk' (D.subgroupOf J) ⟨a,ha⟩,Subtype.ext he⟩

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem suzuki_seed_le_derived_sup_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex F} (hab : (graph F).Adj a b)
    {n : ℕ} (hn : 0 < n)
    (e : (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) ≃* SuzukiMatrixGroup n)
    (J D A : Subgroup G) (hJA : J ≤ A)
    (hAS : A ≤ (stabilizer F a ⊓ stabilizer F b).pCoreIn 2)
    (hcover : (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = A ⊔ Q F a)
    (hD : D ≤ Q F a)
    [(D.subgroupOf J).Normal] [IsElementaryAbelian 2 (J ⧸ D.subgroupOf J)] :
    J ≤ ⁅A,A⁆ ⊔ (A ⊓ Q F a) := by
  let := finite_endpoints h
  let L := graphLocalGroup F a
  let E := stabilizer F a ⊓ stabilizer F b
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hab
  have hES := sylow_image_eq_edge_core (stabilizer F a) E inf_le_left
    (source_edge_core_sylow h hB hab) T hT
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le (H := L) (sylowGenerated_le _)
    (sylow_le_sylowGenerated _ T)
  have hRS : (R : Subgroup L).map L.subtype = E.pCoreIn 2 := hR.trans hES
  have hSL : E.pCoreIn 2 ≤ L := hRS ▸ map_subtype_le _
  have hAL : A ≤ L := hAS.trans hSL
  have hJL : J ≤ L := hJA.trans hAL
  have hQL : Q F a ≤ L := (graph_Q_le_edgeCore h hab).trans hSL
  have hRs : (R : Subgroup L) = (E.pCoreIn 2).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hRS,map_subgroupOf_eq_of_le hSL]
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hc : L.pCoreIn 2 = Q F a := sylowGenerated_core _
  have hk : q.ker = (Q F a).subgroupOf L := by
    rw [←hc]
    change q.ker = ((pCore 2 L).map L.subtype).comap L.subtype
    rw [comap_map_eq_self_of_injective L.subtype_injective]
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let R' := R.mapSurjective hq
  have hsup : A.subgroupOf L ⊔ q.ker = (R : Subgroup L) := by
    rw [hk,←subgroupOf_sup hAL hQL,←hcover,←hRs]
  have hIA : (A.subgroupOf L).map q = (R' : Subgroup (SuzukiMatrixGroup n)) := by
    change _ = (R : Subgroup L).map q
    rw [←hsup,Subgroup.map_sup,Subgroup.map_ker_self,sup_bot_eq]
  let J₀ := J.subgroupOf L
  let : IsElementaryAbelian 2 (J₀.map q) :=
    elementary_image_of_section J D L hJL q (hk ▸ comap_mono hD)
  have hJomega : J₀.map q ≤ omegaOneAmbient (R' : Subgroup (SuzukiMatrixGroup n)) := by
    rw [←omegaOneAmbient_eq_self (J₀.map q)]
    exact omegaOneAmbient_mono ((map_mono (comap_mono hJA)).trans hIA.le)
  have hderived : J₀.map q ≤ (⁅A.subgroupOf L,A.subgroupOf L⁆).map q := by
    rw [map_commutator,hIA,suzukiSylow_commutator_eq_omega hn (MulEquiv.refl _) R']
    exact hJomega
  have hlift : J₀ ≤ ⁅A.subgroupOf L,A.subgroupOf L⁆ ⊔ q.ker := by
    rw [←comap_map_eq]
    exact (le_comap_map q J₀).trans (comap_mono hderived)
  intro x hx
  obtain ⟨y,hy,z,hz,he⟩ := mem_sup_of_normal_right.mp (hlift (show (⟨x,hJL hx⟩ : L) ∈ J₀ from hx))
  have hyA : (y : G) ∈ A := by
    have hm := mem_map_of_mem L.subtype hy
    rw [map_commutator,map_subgroupOf_eq_of_le hAL] at hm
    exact (le_normalizer_iff_commutator_le_left.mp A.le_normalizer) hm
  have hyder : (y : G) ∈ ⁅A,A⁆ := by
    have hm := mem_map_of_mem L.subtype hy
    rwa [map_commutator,map_subgroupOf_eq_of_le hAL] at hm
  have hzQ : (z : G) ∈ Q F a := by
    change z ∈ (Q F a).subgroupOf L
    rwa [←hk]
  have hzA : (z : G) ∈ A := by
    have hev : (y : G)*(z : G) = x := congrArg Subtype.val he
    have hh := A.mul_mem (A.inv_mem hyA) (hJA hx)
    rwa [←hev,inv_mul_cancel_left] at hh
  have hev : (y : G)*(z : G) = x := congrArg Subtype.val he
  rw [←hev]
  exact (⁅A,A⁆ ⊔ (A ⊓ Q F a)).mul_mem (mem_sup_left hyder) (mem_sup_right ⟨hzA,hzQ⟩)


/-- A nonbinary Suzuki beta quotient is incompatible with the earlier
center action and the nonnormal adjacent-core intersection. -/
theorem BTwoCenterActionData.not_suzuki_beta
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    {n : ℕ} (hn : 0 < n)
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SuzukiMatrixGroup n) :
    False := by
  let := finite_endpoints h
  let : Finite (Q F v) := Finite.of_injective
    (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q F v)) := ⟨isPGroup_pCoreIn 2 (stabilizer F v)⟩
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  let J := centralSeed F v m t
  have hJQ : J ≤ Q F v := sup_le (sup_le inf_le_right inf_le_right) d.separated
  have hQv : Q F v ≤ (stabilizer F m ⊓ stabilizer F v).pCoreIn 2 := by
    simpa only [inf_comm] using graph_Q_le_edgeCore h c.middle
  have hQm := graph_Q_le_edgeCore h c.middle.symm
  have hcover : (stabilizer F m ⊓ stabilizer F v).pCoreIn 2 = Q F v ⊔ Q F m := by
    obtain ⟨T,hT⟩ := c.core_product_sylow h
    have he := inf_eq_sylow_map T (isPGroup_pCoreIn 2 (stabilizer F m ⊓ stabilizer F v))
      (hT ▸ sup_le hQm hQv)
    rw [inf_of_le_left ((pCoreIn_le 2 _).trans inf_le_right),hT] at he
    exact he.trans (sup_comm _ _)
  obtain ⟨hN,hE⟩ := c.central_seed_elementary h hB hSyl hb hactor hcentral ht hne hcomm
  let := hN
  let := hE
  have hJder := suzuki_seed_le_derived_sup_intersection h hB hSyl c.middle.symm hn e
    J (D F m t) (Q F v) hJQ hQv hcover inf_le_left
  have hderPhi : ⁅Q F v,Q F v⁆ ≤ (frattini (Q F v)).map (Q F v).subtype := by
    have hh := map_mono (f := (Q F v).subtype)
      (commutator_le_frattini_of_isPGroup (p := 2) (R := Q F v))
    simpa only [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
  exact c.seed_not_le_frattini_sup_intersection h hB hSyl hb hactor hcentral ht hne hcomm hnot
    (hJder.trans (sup_le_sup hderPhi le_rfl))

/-- Every Suzuki parameter, including Sz(2), is excluded on the actual beta quotient. -/
theorem BTwoCenterActionData.not_suzuki_beta_all
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    {n : ℕ}
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SuzukiMatrixGroup n) :
    False := by
  cases n with
  | zero =>
    exact c.not_beta_sylow_omega_le_frattini h hB hSyl hb hactor hcentral ht hne hcomm hnot e
      smallSuzuki_omega_le_frattini
  | succ n =>
    exact c.not_suzuki_beta h hB hSyl hb hactor hcentral ht hne hcomm hnot (Nat.succ_pos n) e

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
