module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoIntrinsicCoreOrders

/-!
# Binary alpha-core centralizers in the strict separation argument

On the actual quotient Q_alpha/D_alpha, the two neighboring radius/core
factors give complementary coordinate subspaces. Each is fixed by its
corresponding Sylow, and the two Sylows generate the local linear group.
The absence of global fixed vectors identifies each factor image with
the full Sylow fixed space. When the alpha field has order two, every
nontrivial Sylow element generates that Sylow.

Consequently, for r in Q_beta outside Q_alpha, C_Q_alpha(r) is contained
in Q_beta. This is the core-structure implication used at the third
neighbor in DGS (10.8). The original binary-source application constructs
the natural action and binary alpha field internally, retaining the
literal original endpoint inclusions. No exceptional/strict selection
or nonsolvability is assumed.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.7), pp.158--159, and the last contradiction in (10.8), p.162.
The terminal-intersection assembly must still correct its actual actor
into the third core before applying this bound at that vertex.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance binaryCoreAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- In binary alpha field, an element of the neighboring core outside the
alpha core has no centralizer in the alpha core outside their intersection. -/
theorem BTwoCenterActionData.binary_core_centralizer
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B)=pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype≤B)
    (hb : b F=2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor=graphLocalGroup F v) (hk : Nat.card k=2)
    (hcentral : Z F m≤centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t≠m)
    (hcomm : ⁅V F m 1,Q F m⁆≤Z F m)
    (hnot : ¬stabilizer F v≤normalizer ((Q F m⊓Q F v : Subgroup G):Set G))
    (eβ : (graphLocalGroup F m⧸pCore 2 (graphLocalGroup F m))≃*SL(2,K))
    (r : G) (hr : r∈Q F m) (hrn : r∉Q F v) :
    Q F v⊓centralizer ({r}:Set G)≤Q F m := by
  let := finite_endpoints h
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨hN,hE,σ,d,_,hglobal,_⟩ := c.linear_core_natural_copies h hB hSyl hb hactor
    hcentral ht hne hcomm hnot eβ
  let := hN
  let := hE
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨a,ha,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  let A := V F m 1⊓Q F v
  let C := V F t 1⊓Q F v
  let D₀ := D F m t
  have hgen : Q F v=(A⊔C)⊔D₀ :=
    (c.linear_seed_eq_core_and_index h hB hSyl hS hb ht hne hnot eβ).1.symm
  have hVm : V F m 1≤Q F m := graph_V_le_Q_of_short h hS m (by rw [hb]; decide)
  have hVt : V F t 1≤Q F t := graph_V_le_Q_of_short h hS t (by rw [hb]; decide)
  have hZD : Z F v≤D₀ := by
    change Z F v≤D F m t
    rw [a.decomposition h hS hb]
    exact le_sup_left
  have hZmD := (center_le_of_central_neighbor h hB hSyl c.middle hcentral).trans hZD
  have hfixed : ⁅V F m 1,A⁆≤D₀ :=
    ((commutator_mono le_rfl (inf_le_left.trans hVm)).trans hcomm).trans hZmD
  have hinter : (A⊔D₀)⊓(C⊔D₀)=D₀ := by
    apply le_antisymm
    · exact inf_le_inf (sup_le (inf_le_left.trans hVm) inf_le_left)
        (sup_le (inf_le_left.trans hVt) inf_le_right)
    · exact le_inf le_sup_right le_sup_right
  have hconj : C=A.conjBy (g:G) := by
    dsimp only [A,C]
    rw [conjBy,map_inf _ _ _ (MulAut.conj (g:G)).injective,←V_translate,←Q_translate,hg,
      show (g:G) • v=v from c.actor_le g.property]
  have hcompl := d.isCompl_imageSpace (A⊔D₀) (C⊔D₀)
    (hgen.trans (by ac_rfl)) hinter.symm
  rw [d.imageSpace_sup_kernel A inf_le_right,d.imageSpace_sup_kernel C inf_le_right] at hcompl
  have hA : d.imageSpace A≤fixedSpace σ c.imageSylow := by
    intro z hz s
    obtain ⟨q,hq,he⟩ := (show (s:SL(2,k))∈((V F m 1).subgroupOf c.actor).map c.quotient from
      (c.radius_image h hS hb).symm ▸ s.property)
    change σ s.val z=z
    rw [←he]
    exact d.fixed_on_imageSpace_of_commutator_le (V F m 1) A hfixed q hq z hz
  let T : Subgroup SL(2,k) := (c.imageSylow:Subgroup SL(2,k)).map
    (MulAut.conj (c.quotient g)).toMonoidHom
  have hC : d.imageSpace C≤fixedSpace σ T := by
    rw [hconj,d.imageSpace_conjBy A inf_le_right]
    rw [show T=(c.imageSylow:Subgroup SL(2,k)).map
      (MulAut.conj (c.quotient g)).toMonoidHom from rfl,
      SL2SylowFixedRecognition.fixedSpace_conjugate]
    exact Submodule.map_mono hA
  have hST : (c.imageSylow:Subgroup SL(2,k))⊔T=⊤ :=
    Matrix.SpecialLinearGroup.sylow_sup_conjugate_eq_top_of_not_mem_normalizer c.imageSylow hop
  have hi : fixedSpace σ c.imageSylow⊓fixedSpace σ T=⊥ :=
    (σ.invariants_comp_sup (c.imageSylow:Subgroup SL(2,k)) T).symm.trans
      ((congrArg (fixedSpace σ) hST).trans hglobal)
  have hfixeq : fixedSpace σ c.imageSylow=d.imageSpace A := by
    apply le_antisymm ?_ hA
    intro z hz
    have hz' : z∈d.imageSpace A⊔d.imageSpace C := hcompl.sup_eq_top.symm ▸ Submodule.mem_top
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hz'
    have hbS : b∈fixedSpace σ c.imageSylow := by
      simpa only [add_sub_cancel_left] using (fixedSpace σ c.imageSylow).sub_mem hz (hA ha)
    have hb0 : b=0 := by
      have hh : b∈fixedSpace σ c.imageSylow⊓fixedSpace σ T := ⟨hbS,hC hb⟩
      simpa only [hi,Submodule.mem_bot] using hh
    simpa only [hb0,add_zero] using ha
  let rL : c.actor := ⟨r,c.neighbor_core_le hr⟩
  have hrS : c.quotient rL∈(c.imageSylow:Subgroup SL(2,k)) :=
    c.neighbor_image ▸ mem_map_of_mem c.quotient (show rL∈(Q F m).subgroupOf c.actor from hr)
  have hr1 : c.quotient rL≠1 := fun he => hrn (show rL∈(Q F v).subgroupOf c.actor from
    c.kernel ▸ (show rL∈c.quotient.ker from he))
  have hScard : Nat.card c.imageSylow=2 :=
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 c.imageSylow).symm.toEquiv).trans hk
  have hzpow : zpowers (c.quotient rL)=(c.imageSylow:Subgroup SL(2,k)) := by
    have hl : zpowers (c.quotient rL)≤(c.imageSylow:Subgroup SL(2,k)) := zpowers_le.mpr hrS
    have hp : (c.quotient rL)^2=1 := by
      have hh := pow_card_eq_one' (x:=(⟨c.quotient rL,hrS⟩:(c.imageSylow:Subgroup SL(2,k))))
      rw [hScard] at hh
      exact congrArg Subtype.val hh
    exact eq_of_le_of_card_ge hl (by rw [Nat.card_zpowers,orderOf_eq_prime hp hr1,hScard])
  intro x hx
  have hfix : (d.coordinates ⟨x,hx.1⟩).toAdd∈fixedSpace σ (zpowers (c.quotient rL)) := by
    apply (mem_fixedSpace_zpowers_iff σ _ _).mpr
    apply (d.fixed_coordinate_iff_commutator_mem rL ⟨x,hx.1⟩).mpr
    have he := mem_centralizer_singleton_iff.mp hx.2
    rw [commutatorElement_eq_one_iff_mul_comm.mpr he]
    exact one_mem _
  rw [hzpow,hfixeq,←d.imageSpace_sup_kernel A inf_le_right] at hfix
  exact (sup_le (inf_le_left.trans hVm) inf_le_left)
    ((d.coordinates_mem_imageSpace_iff_of_kernel_le (A⊔D₀) le_sup_right ⟨x,hx.1⟩).mp hfix)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The binary core-centralizer bound in the literal original endpoint groups.
Both the natural action and its binary field are constructed from F1.11. -/
theorem original_bTwo_binary_core_centralizer
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (e : (L 1 ⧸ pCore 2 (L 1))≃*PSL(2,K)) (hK : Nat.card K=2)
    (r : G) (hr : r∈(parabolic L S 1).pCoreIn 2)
    (hrn : r∉(parabolic L S 0).pCoreIn 2) :
    (parabolic L S 0).pCoreIn 2⊓centralizer ({r}:Set G)≤(parabolic L S 1).pCoreIn 2 := by
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let H := reduced_triple h
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hk : Nat.card k=2 := by
    have hh := (c.linear_central_core_structure H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm.le hnot eβ).1
    have hlo : 1<Nat.card k := Finite.one_lt_card
    rw [hK] at hh
    omega
  have hrmap : r∈(Q F β).map ι := (reduced_base_Q_map h true).symm ▸ hr
  obtain ⟨r₀,hr₀,rfl⟩ := hrmap
  have hr₀n : r₀∉Q F α := fun hh => hrn ((reduced_base_Q_map h false) ▸ mem_map_of_mem ι hh)
  have hbound := c.binary_core_centralizer H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hk hcentral ht htne hcomm.le hnot eβ r₀ hr₀ hr₀n
  intro x hx
  have hxmap : x∈(Q F α).map ι := (reduced_base_Q_map h false).symm ▸ hx.1
  obtain ⟨x₀,hx₀,rfl⟩ := hxmap
  have hc₀ : x₀∈centralizer ({r₀}:Set (G₀ L S)) := by
    apply mem_centralizer_singleton_iff.mpr
    apply (G₀ L S).subtype_injective
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hx.2
  exact (reduced_base_Q_map h true) ▸ mem_map_of_mem ι (hbound ⟨hx₀,hc₀⟩)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
