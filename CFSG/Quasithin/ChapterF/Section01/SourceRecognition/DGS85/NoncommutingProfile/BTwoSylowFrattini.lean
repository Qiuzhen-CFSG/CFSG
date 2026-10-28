module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCubic
public import Theory.Frattini.BinarySquares
/-!
# The beta Sylow cannot have its involutions in its Frattini subgroup

The alpha core maps onto a Sylow subgroup of the actual beta quotient.
The seed image is a normal elementary subgroup of that Sylow. If every
such subgroup lies in Frattini, its image lies there too. Surjectivity on Frattini subgroups of finite
two-groups then lifts this inclusion to Phi(Q_alpha) times the adjacent
core intersection, contradicting the source seed Frattini obstruction.

The original first-omega criterion is retained as a corollary and is
discharged for binary unitary carriers in BTwoUnitaryExclusion. The normal
elementary criterion also applies to the semidihedral order-144 enlargement. No saturation or classification conclusion is an input.
Source: DGS, Groups and Graphs (1985), (10.7), printed pp.158--159.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G]

private theorem frattini_map_surjective_two {H K : Type*} [Group H] [Group K]
    [Finite H] [Finite K] (f : H →* K) (hf : Function.Surjective f)
    (hH : IsPGroup 2 H) : (frattini H).map f = frattini K := by
  rw [hH.frattini_eq_closure_squares,
    (hH.of_surjective f hf).frattini_eq_closure_squares, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    exact ⟨f x,(map_pow f x 2).symm⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨x,rfl⟩ := hf z
    exact ⟨x^2,⟨x,rfl⟩,map_pow f x 2⟩

private theorem frattini_image_map_two {H K : Type*} [Group H] [Group K]
    (A : Subgroup H) [Finite A] (f : H →* K) (hA : IsPGroup 2 A) :
    (frattini (A.map f)).map (A.map f).subtype =
      ((frattini A).map A.subtype).map f := by
  let : Finite (A.map f) := Finite.of_surjective (f.subgroupMap A) (f.subgroupMap_surjective A)
  rw [←frattini_map_surjective_two (f.subgroupMap A) (f.subgroupMap_surjective A) hA,
    map_map,map_map]
  rfl

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

private theorem seed_le_frattini_sup_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex F} (hab : (graph F).Adj a b)
    {H : Type*} [Group H] [Finite H]
    (e : (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) ≃* H)
    (hNormalElem : ∀ (T : Sylow 2 H) (E : Subgroup H), E ≤ T →
      T ≤ normalizer (E : Set H) → IsElementaryAbelian 2 E →
      E ≤ (frattini T).map (T : Subgroup H).subtype)
    (J D A : Subgroup G) (hJA : J ≤ A) (hnJ : A ≤ normalizer (J : Set G))
    (hAS : A ≤ (stabilizer F a ⊓ stabilizer F b).pCoreIn 2)
    (hcover : (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = A ⊔ Q F a)
    (hD : D ≤ Q F a)
    [(D.subgroupOf J).Normal] [IsElementaryAbelian 2 (J ⧸ D.subgroupOf J)] :
    J ≤ (frattini A).map A.subtype ⊔ (A ⊓ Q F a) := by
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
  have hIA : (A.subgroupOf L).map q = (R' : Subgroup (H)) := by
    change _ = (R : Subgroup L).map q
    rw [←hsup,Subgroup.map_sup,Subgroup.map_ker_self,sup_bot_eq]
  let J₀ := J.subgroupOf L
  let : IsElementaryAbelian 2 (J₀.map q) :=
    elementary_image_of_section J D L hJL q (hk ▸ comap_mono hD)
  have hJR : J₀.map q ≤ (R' : Subgroup H) :=
    (map_mono (comap_mono hJA)).trans hIA.le
  have hnorm : (R' : Subgroup H) ≤ normalizer (J₀.map q : Set H) := by
    rw [←hIA]
    exact (map_mono ((comap_mono hnJ).trans (le_normalizer_comap L.subtype))).trans
      (le_normalizer_map q)
  have hJphi := hNormalElem R' (J₀.map q) hJR hnorm inferInstance
  let A₀ := A.subgroupOf L
  have hA : IsPGroup 2 A :=
    (isPGroup_pCoreIn 2 (stabilizer F a ⊓ stabilizer F b)).of_injective
      (inclusion hAS) (inclusion_injective _)
  have hAp : IsPGroup 2 A₀ := hA.comap_subtype
  have hphi : ((frattini A₀).map A₀.subtype).map q =
      (frattini R').map (R' : Subgroup H).subtype := by
    rw [←frattini_image_map_two A₀ q hAp, hIA]
  have hderived : J₀.map q ≤ ((frattini A₀).map A₀.subtype).map q :=
    hJphi.trans_eq hphi.symm
  have hlift : J₀ ≤ (frattini A₀).map A₀.subtype ⊔ q.ker := by
    rw [←comap_map_eq]
    exact (le_comap_map q J₀).trans (comap_mono hderived)
  intro x hx
  obtain ⟨y,hy,z,hz,he⟩ := mem_sup_of_normal_right.mp (hlift (show (⟨x,hJL hx⟩ : L) ∈ J₀ from hx))
  have hyder : (y : G) ∈ (frattini A).map A.subtype := by
    have hm := mem_map_of_mem L.subtype hy
    rwa [←frattini_image_map A₀ L.subtype L.subtype_injective,
      map_subgroupOf_eq_of_le hAL] at hm
  have hyA : (y : G) ∈ A := map_subtype_le _ hyder
  have hzQ : (z : G) ∈ Q F a := by
    change z ∈ (Q F a).subgroupOf L
    rwa [←hk]
  have hzA : (z : G) ∈ A := by
    have hev : (y : G)*(z : G) = x := congrArg Subtype.val he
    have hh := A.mul_mem (A.inv_mem hyA) (hJA hx)
    rwa [←hev,inv_mul_cancel_left] at hh
  have hev : (y : G)*(z : G) = x := congrArg Subtype.val he
  rw [←hev]
  exact ((frattini A).map A.subtype ⊔ (A ⊓ Q F a)).mul_mem (mem_sup_left hyder) (mem_sup_right ⟨hzA,hzQ⟩)


/-- The seed is normal in the actual beta Sylow, so normal elementary
Frattini containment already contradicts source movement. -/
theorem BTwoCenterActionData.not_beta_normal_elementary_le_frattini
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
    {H : Type*} [Group H] [Finite H]
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* H)
    (hNormalElem : ∀ (T : Sylow 2 H) (E : Subgroup H), E ≤ T →
      T ≤ normalizer (E : Set H) → IsElementaryAbelian 2 E →
      E ≤ (frattini T).map (T : Subgroup H).subtype) :
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
  have hnJ : Q F v ≤ normalizer (J : Set G) :=
    (Q_le_stabilizer F v).trans (c.seed_stabilizer_normalized h hS hb ht hne)
  have hJphi := seed_le_frattini_sup_intersection h hB hSyl c.middle.symm e hNormalElem
    J (D F m t) (Q F v) hJQ hnJ hQv hcover inf_le_left
  exact c.seed_not_le_frattini_sup_intersection h hB hSyl hb hactor hcentral ht hne hcomm hnot hJphi

/-- The central noncommuting configuration excludes every actual beta
quotient whose Sylow involutions lie in the Sylow Frattini subgroup. -/
theorem BTwoCenterActionData.not_beta_sylow_omega_le_frattini
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
    {H : Type*} [Group H] [Finite H]
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* H)
    (hΩ : ∀ T : Sylow 2 H, omegaOneAmbient (T : Subgroup H) ≤
      (frattini T).map (T : Subgroup H).subtype) :
    False := by
  apply c.not_beta_normal_elementary_le_frattini h hB hSyl hb hactor hcentral
    ht hne hcomm hnot e
  intro T E hET _ hE
  let := hE
  apply le_trans ?_ (hΩ T)
  rw [←omegaOneAmbient_eq_self E]
  exact omegaOneAmbient_mono hET

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
