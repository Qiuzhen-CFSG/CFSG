module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Quotient
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.CubicBlocks
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NondegeneratePlane.Lift

/-!
# The actual pair lifted from a nondegenerate plane

Lift the two native cubic axes through the original L→A₆ map. The source
moving-space identity gives complementary four-groups inside the original V;
the cross-fixation identities make their A₃ extensions commute. Their join
is V(P₁P₂), with two-core exactly V and the marked native image normalized
by the full plane stabilizer. Possible central two-covers of L are retained.

Source: Aschbacher–Smith13.5.6, printed p.917.
-/

@[expose] public section
open Subgroup BinaryPermutation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing NondegeneratePlane
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)

theorem actor_map_local (P:Subgroup L) :
    (actor d (P.map L.subtype) ((map_subtype_le P).trans le_sup_left)).range = P.map (localMap d) := by
  ext a
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨l,hl,he⟩:=x.property
    refine ⟨l,hl,?_⟩
    change localMap d l=permutation d ⟨x.val,_⟩
    change (d.local_quotient (QuotientGroup.mk' _ l)).val=_
    rw [←permutation_L d l]
    congr 1
    exact Subtype.ext he
  · rintro ⟨l,hl,rfl⟩
    refine ⟨⟨l.val,⟨l,hl,rfl⟩⟩,?_⟩
    exact permutation_L d l

structure CubicPair (W:Subgroup G) where
  first : Subgroup L
  second : Subgroup L
  elementary : IsElementaryAbelian 3 (first⊔second : Subgroup L)
  card : Nat.card (first⊔second : Subgroup L)=9
  image_stabilizes : (first⊔second).map (localMap d)≤flagStabilizer (image d W)
  image_normalized : flagStabilizer (image d W)≤normalizer ((first⊔second).map (localMap d) : Set _)
  first_block : ChapterC.IsAlternatingBlock (⁅V,first.map L.subtype⁆⊔first.map L.subtype : Subgroup G) 3
  second_block : ChapterC.IsAlternatingBlock (⁅V,second.map L.subtype⁆⊔second.map L.subtype : Subgroup G) 3
  commuting : (⁅V,first.map L.subtype⁆⊔first.map L.subtype) ≤
    centralizer ((⁅V,second.map L.subtype⁆⊔second.map L.subtype : Subgroup G):Set G)
  join : (⁅V,first.map L.subtype⁆⊔first.map L.subtype)⊔
    (⁅V,second.map L.subtype⁆⊔second.map L.subtype)=V⊔(first⊔second).map L.subtype
  product : Nonempty ((V⊔(first⊔second).map L.subtype : Subgroup G)≃*AlternatingFourPair.Model)
  core : (V⊔(first⊔second).map L.subtype).pCoreIn 2=V

theorem exists_cubicPair (hb:ChapterC.IsAlternatingBlock L 6)
    (W:Subgroup G) (hWV:W≤V) (hcard:Nat.card W=4)
    (hn:¬∀x∈image d W,∀y∈image d W,form x y=0) : Nonempty (CubicPair d W) := by
  have hd : Module.finrank (ZMod 2) (image d W)=2 := image_dim d W hWV 2 hcard
  obtain ⟨P,Q,hP,hQ,_,hPQ,hE,h9,hst,hnP,hnQ,hmP,hmQ,hfP,hfQ⟩ :=
    exists_lifted_cubic_decomposition (localMap d) (localMap_range d) (localMap_kernel_two d hb)
      (image d W) hd hn
  let A:=P.map L.subtype
  let B:=Q.map L.subtype
  have hAL:A≤L⊔(T:Subgroup G):=(map_subtype_le P).trans le_sup_left
  have hBL:B≤L⊔(T:Subgroup G):=(map_subtype_le Q).trans le_sup_left
  have ha:Nat.card A=3:=(card_map_of_injective L.subtype_injective).trans hP
  have hb:Nat.card B=3:=(card_map_of_injective L.subtype_injective).trans hQ
  have hc:A≤centralizer (B:Set G):=by
    rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩
    exact congrArg Subtype.val (hPQ p hp q hq).symm.eq
  have hmA:image d ⁅V,A⁆=image d W:=by
    rw [image_commutator d A hAL]
    exact (congrArg movedSpace (actor_map_local d P)).trans hmP
  have hmB:image d ⁅V,B⁆=form.orthogonal (image d W):=by
    rw [image_commutator d B hBL]
    exact (congrArg movedSpace (actor_map_local d Q)).trans hmQ
  have hcompl:=nondegeneratePlane_isCompl (image d W) hd hn
  have huA:Nat.card (image d ⁅V,A⁆)=4:=by rw [hmA,image_card d W hWV,hcard]
  have hdperp:Module.finrank (ZMod 2) (form.orthogonal (image d W))=2:=by
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,hd,
      finrank_natural_even (Fin 6) (by decide)]
    norm_num
  have huB:Nat.card (image d ⁅V,B⁆)=4:=by
    rw [hmB,Module.natCard_eq_pow_finrank (K:=ZMod 2),hdperp,Nat.card_eq_fintype_card,ZMod.card]
    rfl
  have hfixedA:∀a∈(actor d A hAL).range,∀v∈image d ⁅V,B⁆,naturalRepresentation (Fin 6) a v=v:=by
    rw [actor_map_local d P,hmB]
    exact hfP
  have hfixedB:∀a∈(actor d B hBL).range,∀v∈image d ⁅V,A⁆,naturalRepresentation (Fin 6) a v=v:=by
    rw [actor_map_local d Q,hmA]
    exact hfQ
  obtain ⟨hba,hbb,hcomm,hjoin,he,hcore⟩:=cubic_blocks_of_axes d A B hAL hBL ha hb hc huA huB
    (by rwa [hmA,hmB]) hfixedA hfixedB
  refine ⟨⟨P,Q,hE,h9,hst,?_,hba,hbb,hcomm,?_,?_,?_⟩⟩
  · rw [Subgroup.map_sup]
    exact (le_inf hnP hnQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · simpa only [A,B,Subgroup.map_sup] using hjoin
  · obtain ⟨e⟩:=he
    have hs : V⊔(P⊔Q).map L.subtype=V⊔(A⊔B) := by rw [Subgroup.map_sup]
    exact ⟨(MulEquiv.subgroupCongr hs).trans e⟩
  · simpa only [A,B,Subgroup.map_sup] using hcore
end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
