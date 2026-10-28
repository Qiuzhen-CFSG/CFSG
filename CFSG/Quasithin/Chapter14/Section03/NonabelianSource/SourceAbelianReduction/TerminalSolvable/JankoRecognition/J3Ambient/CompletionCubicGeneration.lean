module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.InvolutionCentralizerContainment
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.StrongEmbeddingExclusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.OutsideInvolutionFusion
public import BenderSuzuki.SE.SingleInvolutionClass
public import Theory.GroupTheory.CyclicHallNormalizerEscape
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.InvolutionCoreReturning
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.InvolutionOutsideReturning

/-!
# Generation by the literal completion and cubic normalizer

The join contains the full centralizer of the literal field involution.
The actual field subgroup returns that involution outside its core, while
the actual cubic centralizer returns it to a noncentral core involution.
The three local classes therefore fuse within the same join. Odd relative
index gives a single involution class in the join itself, so strong-embedding
exclusion forces the join to be the whole original group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen

variable {G : Type*} [Group G] [Finite G] {D : Seed G} {f : G}

private theorem central_core_involution_eq
    (h : Janko23.HTypeAt f)
    (x : Janko23.localCore f) (hx : orderOf ((x : Janko23.involutionCentralizer f) : G) = 2)
    (hxZ : x ∈ center (Janko23.localCore f)) :
    ((x : Janko23.involutionCentralizer f) : G) = f := by
  let e : Janko23.localCore f ≃* Janko23.ambientCore f :=
    (Janko23.localCore f).equivMapOfInjective _
      (Janko23.involutionCentralizer f).subtype_injective
  have heZ : e x ∈ center (Janko23.ambientCore f) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨y,rfl⟩ := e.surjective q
    exact (e.map_mul y x).symm.trans
      ((congrArg e (mem_center_iff.mp hxZ y)).trans (e.map_mul x y))
  have hxline : ((x : Janko23.involutionCentralizer f) : G) ∈ zpowers f :=
    h.core_center_image ▸ mem_map_of_mem (Janko23.ambientCore f).subtype heZ
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨((x : Janko23.involutionCentralizer f) : G),hxline⟩ : zpowers f))
    (y := (⟨f,mem_zpowers f⟩ : zpowers f))
    ((orderOf_coe _).symm.trans hx) ((orderOf_coe _).symm.trans h.involution))

private theorem centralizer_involution_fusion_of_returning_witnesses
    (h : Janko23.HTypeAt f)
    (M : Subgroup G) (hHM : Janko23.involutionCentralizer f ≤ M)
    (u v : G) (huQ : u ∈ Janko23.ambientCore f) (hu : orderOf u = 2) (huf : u ≠ f)
    (hvH : v ∈ Janko23.involutionCentralizer f) (hv : orderOf v = 2)
    (hvQ : v ∉ Janko23.ambientCore f)
    (hfu : ∃ n ∈ M, n*f*n⁻¹ = u) (hfv : ∃ n ∈ M, n*f*n⁻¹ = v)
    (y : G) (hyH : y ∈ Janko23.involutionCentralizer f) (hy : orderOf y = 2) :
    ∃ m ∈ M, m*f*m⁻¹ = y := by
  let H := Janko23.involutionCentralizer f
  let yH : H := ⟨y,hyH⟩
  have hyH2 : orderOf yH = 2 := (orderOf_coe yH).symm.trans hy
  by_cases hyf : y = f
  · exact ⟨1,one_mem _,by simp [hyf]⟩
  by_cases hyQ : y ∈ Janko23.ambientCore f
  · have hyQ' : yH ∈ Janko23.localCore f := by
      rw [←Janko23.ambientCore_subgroupOf]
      exact hyQ
    let yQ : Janko23.localCore f := ⟨yH,hyQ'⟩
    have hyZ : yQ ∉ center (Janko23.localCore f) :=
      fun hh => hyf (central_core_involution_eq h yQ hy hh)
    let uH : H := ⟨u,Janko23.ambientCore_le f huQ⟩
    have huQ' : uH ∈ Janko23.localCore f := by
      rw [←Janko23.ambientCore_subgroupOf]
      exact huQ
    let uQ : Janko23.localCore f := ⟨uH,huQ'⟩
    have huZ : uQ ∉ center (Janko23.localCore f) :=
      fun hh => huf (central_core_involution_eq h uQ hu hh)
    have huQ2 : orderOf uQ = 2 :=
      (orderOf_coe uQ).symm.trans ((orderOf_coe uH).symm.trans hu)
    have hyQ2 : orderOf yQ = 2 := (orderOf_coe yQ).symm.trans hyH2
    obtain ⟨g,hg⟩ := isConj_iff.mp
      (h.core_noncentral_involutions_isConj uQ yQ huQ2 huZ hyQ2 hyZ)
    obtain ⟨n,hn,he⟩ := hfu
    refine ⟨(g : G)*n,mul_mem (hHM g.property) hn,?_⟩
    have hgy : (g : G)*u*(g : G)⁻¹ = y := congrArg Subtype.val hg
    calc
      ((g : G)*n)*f*((g : G)*n)⁻¹ = (g : G)*(n*f*n⁻¹)*(g : G)⁻¹ := by group
      _ = y := by rw [he,hgy]
  · let vH : H := ⟨v,hvH⟩
    obtain ⟨g,hg⟩ := isConj_iff.mp (h.outside_involutions_isConj vH yH
      ((orderOf_coe vH).symm.trans hv) hyH2 hvQ hyQ)
    obtain ⟨n,hn,he⟩ := hfv
    refine ⟨(g : G)*n,mul_mem (hHM g.property) hn,?_⟩
    have hgy : (g : G)*v*(g : G)⁻¹ = y := congrArg Subtype.val hg
    calc
      ((g : G)*n)*f*((g : G)*n)⁻¹ = (g : G)*(n*f*n⁻¹)*(g : G)⁻¹ := by group
      _ = y := by rw [he,hgy]

private theorem eq_top_of_returning_witnesses
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G) (h : Janko23.HTypeAt f)
    (M : Subgroup G) (hHM : Janko23.involutionCentralizer f ≤ M)
    (u v : G) (huQ : u ∈ Janko23.ambientCore f) (hu : orderOf u = 2) (huf : u ≠ f)
    (hvH : v ∈ Janko23.involutionCentralizer f) (hv : orderOf v = 2)
    (hvQ : v ∉ Janko23.ambientCore f)
    (hfu : ∃ n ∈ M, n*f*n⁻¹ = u) (hfv : ∃ n ∈ M, n*f*n⁻¹ = v) : M = ⊤ := by
  let H := Janko23.involutionCentralizer f
  have hindex : ¬2 ∣ (H.subgroupOf M).index := by
    have ho := h.centralizer_odd_index hc
    exact fun hd => (Nat.not_even_iff_odd.mpr ho)
      (even_iff_two_dvd.mpr (dvd_trans hd (relIndex_dvd_index_of_le hHM)))
  have hfM : f ∈ M := hHM (mem_centralizer_singleton_iff.mpr rfl)
  by_contra hproper
  apply literal_not_strongly_embedded P M
  apply BenderSuzuki.isStronglyEmbedded_of_single_involution_class M hproper f
    h.involution hfM hHM
  intro y hyM hy
  let yM : M := ⟨y,hyM⟩
  have hy2 : orderOf yM = 2 := (orderOf_coe yM).symm.trans hy
  have hp : IsPGroup 2 (zpowers yM) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hy2)
  obtain ⟨g,hg⟩ := exists_conj_le_of_prime_not_dvd_index (H.subgroupOf M) (zpowers yM) hindex hp
  have hgyH : (g : G)*y*(g : G)⁻¹ ∈ H :=
    hg (mem_map_of_mem (MulAut.conj g).toMonoidHom (mem_zpowers yM))
  have hgy2 : orderOf ((g : G)*y*(g : G)⁻¹) = 2 :=
    ((MulAut.conj (g : G)).orderOf_eq y).trans hy
  obtain ⟨n,hn,he⟩ := centralizer_involution_fusion_of_returning_witnesses h M hHM
    u v huQ hu huf hvH hv hvQ hfu hfv ((g : G)*y*(g : G)⁻¹) hgyH hgy2
  refine ⟨(g : G)⁻¹*n,mul_mem (inv_mem g.property) hn,?_⟩
  calc
    ((g : G)⁻¹*n)*f*((g : G)⁻¹*n)⁻¹ = (g : G)⁻¹*(n*f*n⁻¹)*(g : G) := by group
    _ = y := by rw [he]; group

open Janko23.J3Recognition.Ambient Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- The same literal field completion and cubic normalizer generate the
whole original group, with both returning witnesses proved from the source. -/
theorem literal_completion_cubic_normalizer_generate
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    completion j.range (overlap j) ⊔ normalizer (zpowers (j cubic) : Set G) = ⊤ := by
  have hf : orderOf (j SingerField.fieldElement) = 2 := image_involution_order j hj.1
  have hlocal := literal_involution_localType (D := D) hc _ hf
  have hHM := literal_involution_centralizer_le_completion_sup_cubic_normalizer P hc A C a j hj
  obtain ⟨u,huQ,hu,huf,r,hr,hru⟩ := literal_field_core_returning P hc A C a j hj
  obtain ⟨v,hvH,hv,hvQ,t,ht,htv⟩ := literal_field_outside_returning P hc A C a j hj
  apply eq_top_of_returning_witnesses P hc hlocal _ hHM u v huQ hu huf hvH hv hvQ
  · exact ⟨r,mem_sup_right (cubic_centralizer_le_normalizer (j cubic) hr),hru⟩
  · exact ⟨t,mem_sup_left (mem_sup_left ht),htv⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
