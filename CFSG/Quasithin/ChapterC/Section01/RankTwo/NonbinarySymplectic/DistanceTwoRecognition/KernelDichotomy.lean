module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedKernelComparison
public import Theory.Representation.SymplecticFourOrthogonalCover.RootTranslations
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The maximal fixed-kernel comparison at distance two

Translating a root displacement by any nonidentity element of its full
fixed kernel makes one of the two elements an individual commutator.
A common fixed-kernel element therefore forces containment of the opposite
kernel: otherwise one of those two commutators is nontrivial and fixed at
the opposite endpoint, contradicting fixed-vector lifting. Equal orders
then identify the kernels.

Consequently the full kernels either agree, or they are disjoint, each
has order q, and their product is the complete common displacement.
The last theorem supplies the field-sized premise from the original
odd-index witness. The unequal case is retained; these local identities
do not establish radical saturation or the field restriction.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the fixed-kernel and root-value comparison in (3.7)(4), printed p.875.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A nonidentity fixed-kernel translate of an actual critical displacement
is an individual commutator whenever the original element is not one. -/
theorem replacement_field_sized_paired_commutator_or_mul
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (x : FreeAmalgam d.radical) (hx : x ∈ ⁅Z d.radical a,Z d.radical z⁆)
    (hn : x ∉ U d.radical a ⊓
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)))
    (k : FreeAmalgam d.radical)
    (hk : k ∈ U d.radical a ⊓
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) (hk0 : k ≠ 1) :
    ∃ b ∈ U d.radical z, ∃ u ∈ U d.radical a, ⁅b,u⁆=x ∨ ⁅b,u⁆=x*k := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have haq := (replacement_field_sized_edge_factorization h d rev hb hzt hat hsize).1
  have hzq := (replacement_field_sized_edge_factorization h d path hb hat hzt hsize).1
  have hZA : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZA κ hκQ).trans (hzq.trans hFc.symm)
  have hδ : ∀ x : Z d.radical z, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hZA x) v
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ hδ hδcard (haq.trans hFc.symm)
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hkerImage : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hc,rfl⟩
  let p := MovedSection.coverProjection s e
  have hx' : x ∈ ⁅Z d.radical z,U d.radical a⁆ := by
    rw [commutator_comm,←replacement_field_sized_displacement_eq_moving h d path hb hat hzt hsize]
    exact hx
  obtain ⟨b,hbZ,u,hu,he⟩ := embedded_root_value_or_mul_kernel hcard
    (U d.radical a) (Z d.radical z) p he j hjr β hβ hβcard hβdim hβquad
    x k hx' (by rwa [hkerImage]) (by rwa [hkerImage]) hk0
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  have htz : Z d.radical t ≤ Z d.radical z := Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt
  have hta : Z d.radical t ≤ Z d.radical a := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  have hcent : Z d.radical t ≤ centralizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    htz.trans ((Z d.radical z).le_centralizer.trans (centralizer_le (U_le_Z z)))
  have hbjoin : b ∈ U d.radical z ⊔ Z d.radical t := by
    rwa [←(replacement_field_sized_central_layers h d rev hb hzt hat hsize).2]
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _
    (hcent.trans (Subgroup.centralizer_le_normalizer _))] at hbjoin
  obtain ⟨v,hv,w,hw,rfl⟩ := hbjoin
  have hwu : Commute w u :=
    ((hta.trans ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))) hw u hu).symm
  refine ⟨v,hv,u,hu,?_⟩
  have hv : ⁅v*w,u⁆=⁅v,u⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,commutatorElement_eq_one_iff_commute.mpr hwu]
    simp only [mul_one,mul_inv_cancel,one_mul]
  simpa only [hv] using he

/-- The complete paired fixed kernels either agree or have trivial intersection. -/
theorem replacement_field_sized_fixed_kernels_eq_or_disjoint
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    A=A' ∨ Disjoint A A' := by
  classical
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  obtain ⟨_,hcontain,_,_,hcard⟩ := replacement_field_sized_paired_fixed_layers h d path hb hat hzt hsize
  by_cases heq : A=A'
  · exact Or.inl heq
  right
  apply disjoint_iff_inf_le.mpr
  intro k hk
  change k=1
  by_contra hk0
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hle : A' ≤ A := by
    intro x hx
    by_contra hn
    obtain ⟨b,hbU,u,hu,he⟩ := replacement_field_sized_paired_commutator_or_mul h d path hb hat hzt hsize
      x (hcontain (mem_sup_right hx)) hn k hk.1 hk0
    have hc : ⁅b,u⁆ ∈ A' := by
      rcases he with he | he
      · exact he ▸ hx
      · exact he ▸ A'.mul_mem hx hk.2
    have hc' : ⁅u,b⁆ ∈ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
      rw [←commutatorElement_inv]
      exact inv_mem hc.2
    have he1 := replacement_field_sized_value_in_fixed_eq_one h d rev hb hzt hat hsize
      u (U_le_Z a hu) b hbU hc'
    have he2 : ⁅b,u⁆=1 := commutatorElement_eq_one_iff_commute.mpr
      (commutatorElement_eq_one_iff_commute.mp he1).symm
    rcases he with he | he
    · exact hn (he.symm ▸ he2.symm ▸ A.one_mem)
    · have hxk : x*k ∈ A := he ▸ he2.symm ▸ A.one_mem
      have hxA := A.mul_mem hxk (A.inv_mem hk.1)
      exact hn (by simpa only [mul_inv_cancel_right] using hxA)
  let := finite_Z d.radical a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  exact heq (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

/-- If the complete fixed kernels differ, they are complementary in the
actual common displacement, and each has the full field order. -/
theorem replacement_field_sized_fixed_kernels_dichotomy
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    A=A' ∨ Disjoint A A' ∧ Nat.card A=2^n ∧ Nat.card A'=2^n ∧
      A ⊔ A'=⁅Z d.radical a,Z d.radical z⁆ := by
  classical
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
  by_cases he : A=A'
  · exact Or.inl he
  have hd := (replacement_field_sized_fixed_kernels_eq_or_disjoint h d path hb hat hzt hsize).resolve_left he
  obtain ⟨hA,hA'⟩ := (replacement_field_sized_fixed_kernels_eq_or_full h d path hb hat hzt hsize).resolve_left he
  refine Or.inr ⟨hd,hA,hA',?_⟩
  obtain ⟨_,hle,hWU,hWcard,_⟩ := replacement_field_sized_paired_fixed_layers h d path hb hat hzt hsize
  let := finite_Z d.radical a
  let : Finite (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hWU.trans inf_le_left |>.trans (U_le_Z a))) (inclusion_injective _)
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  have hcent : A' ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    (le_sup_right.trans hle |>.trans hWU |>.trans inf_le_left |>.trans (U_le_Z a)).trans
      ((Z d.radical a).le_centralizer.trans (centralizer_le (inf_le_left.trans (U_le_Z a))))
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_sup_eq_mul_of_normalizes_of_disjoint A A'
    (hcent.trans (Subgroup.centralizer_le_normalizer _)) hd,hWcard,hA,hA']

/-- Apply the dichotomy with the ORIGINAL odd-index radical witness. -/
theorem replacement_proper_nonsylow_fixed_kernels_dichotomy
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    A=A' ∨ Disjoint A A' ∧ Nat.card A=2^n ∧ Nat.card A'=2^n ∧
      A ⊔ A'=⁅Z d.radical a,Z d.radical z⁆ :=
  replacement_field_sized_fixed_kernels_dichotomy h d path hb hat hzt
    (replacement_proper_nonsylow_card h d g hb hnsyl hne)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
