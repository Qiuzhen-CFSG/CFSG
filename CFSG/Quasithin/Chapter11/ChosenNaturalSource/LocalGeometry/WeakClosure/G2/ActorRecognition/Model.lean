module
public import CFSG.Quasithin.ChapterE.Section04.GenerationSetup
public import Theory.Representation.G2NaturalLongRootFixer
public import Theory.Representation.G2NaturalOffenders
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# Locating the original G₂ fixed-space family

An elementary actor with fixed-space parameter greater than the field degree
cannot consist only of long-root involutions. The pure-long fusion theorem
places such an actor in the A-B plane; intersection with one field root has
small enough index to force fixation of a four-space, contradicting its rank.
A short-root involution instead puts the actor in its literal centralizer.
The actual SL₂ quotient has elementary image of order at most q, so the same
fixed-space equality kills this quotient and places the actor in A-B-C.

This is the containment assertion of B.4.6(9), with all model actions and
conjugators specified. Equality at parameter 2n is a further assertion.
The original chosen-module application is in ActorRecognition.Source.
The existing octonion root formulas are from the attributed ATLAS port;
see LICENSES/ATLAS.txt. Source: Aschbacher--Smith, printed pp.88--89,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.ValueBound
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition
open Atlas.G2 Atlas.G2.NaturalOffenders Atlas.G2.LieParabolicSetup
open Atlas.G2.ShortRootProducts.CentralizerCore
variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Finite F]

omit [Algebra (ZMod 2) F] [Finite F] in
private theorem centralizer_le_local (r : F) (hr : r ≠ 0) :
    centralizer ({rootC r} : Set (Model F)) ≤ local₂ := by
  intro g hg
  obtain ⟨p,c,M,rfl⟩ := centralizer_rootC_factor r hr hg
  apply mul_mem
  · exact mul_mem (residualBlock_le_local (mem_sup_left ⟨p,rfl⟩))
      (unipotent_le_local₂ (shortRootGroup_le_unipotent ⟨Multiplicative.ofAdd c,rfl⟩))
  · exact block_mem_local₂ M

omit [Algebra (ZMod 2) F] [Finite F] in
private theorem local_projection_rootC (c : F) :
    longSLHom (⟨rootC c,unipotent_le_local₂
      (shortRootGroup_le_unipotent ⟨Multiplicative.ofAdd c,rfl⟩)⟩ : local₂) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [longSLHom_ker]
  exact ⟨![0,0,c,0,0,0],rfl,by simp [unipotentProduct]⟩

omit [Algebra (ZMod 2) F] [Finite F] in
private theorem centralizer_projection_kernel (r : F) (hr : r ≠ 0)
    (g : centralizer ({rootC r} : Set (Model F)))
    (hg : longSLHom (inclusion (centralizer_le_local r hr) g) = 1) :
    g.val ∈ EvenTwoRank.elementary F := by
  obtain ⟨p,c,M,he⟩ := centralizer_rootC_factor r hr g.property
  have hfactor : (inclusion (centralizer_le_local r hr) g : local₂) =
      (⟨longRootHom p,residualBlock_le_local (mem_sup_left ⟨p,rfl⟩)⟩ : local₂) *
      ⟨rootC c,unipotent_le_local₂
        (shortRootGroup_le_unipotent ⟨Multiplicative.ofAdd c,rfl⟩)⟩ *
      longSLSection M := Subtype.ext he
  rw [hfactor,map_mul,map_mul,local_projection_rootC,longSLHom_section] at hg
  have hp : longSLHom
      (⟨longRootHom p,residualBlock_le_local (mem_sup_left ⟨p,rfl⟩)⟩ : local₂) = 1 :=
    blockProjection_longRoot p
  rw [hp,one_mul,one_mul] at hg
  rw [he,hg,map_one,mul_one]
  exact (EvenTwoRank.elementary F).mul_mem
    ((EvenTwoRank.elementary F).mul_mem (rootA_mem_elementary _) (rootB_mem_elementary _))
    (rootC_mem_elementary _)

/-- In a short-root centralizer, an A_k actor with k > n fixes the natural
three-space and lies in its actual elementary subgroup of order q³. -/
theorem le_elementary_of_shortRoot {n k : ℕ} (hc : Nat.card F = 2^n) (hn : n < k)
    (A : Subgroup (Model F)) (hA : A ∈ fixedSpaceFamily (binaryAction (F:=F)) k)
    (r : F) (hr : r ≠ 0) (hrA : rootC r ∈ A) : A ≤ EvenTwoRank.elementary F := by
  let := hA.2.1.2
  have hAC : A ≤ centralizer ({rootC r} : Set (Model F)) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg (fun x : A => x.val) (mul_comm (⟨a,ha⟩ : A) ⟨rootC r,hrA⟩)
  let j : A →* SL(2,F) := longSLHom.comp
    (inclusion (hAC.trans (centralizer_le_local r hr)))
  have hj2 : IsPGroup 2 j.range :=
    (hA.2.1.2.isPGroup).of_surjective j.rangeRestrict j.rangeRestrict_surjective
  obtain ⟨P,hP⟩ := hj2.exists_le_sylow
  have hjcard : Nat.card j.range ≤ 2^n := by
    have hp : Nat.card P = Nat.card F :=
      (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P).toEquiv).symm
    exact (card_le_of_le hP).trans_eq (hp.trans hc)
  let B := j.ker.map A.subtype
  have hBA : B ≤ A := map_subtype_le _
  have hindex : B.relIndex A = Nat.card j.range := by
    have hh := relIndex_map_map_of_injective j.ker (⊤ : Subgroup A) A.subtype_injective
    simpa only [←MonoidHom.range_eq_map,A.range_subtype,relIndex_top_right,index_ker] using hh
  have hfix : fixedSpace (binaryAction (F:=F)) A = fixedSpace (binaryAction (F:=F)) B := by
    apply hA.2.2 B hBA
    rw [hindex]
    have hh := Nat.log_mono_right (b:=2) hjcard
    rw [Nat.log_pow (by decide : 1<2)] at hh
    omega
  have hBE : B ≤ EvenTwoRank.elementary F := by
    rintro _ ⟨a,ha,rfl⟩
    exact centralizer_projection_kernel r hr ⟨a.val,hAC a.property⟩ ha
  intro a ha
  apply mem_elementary_of_centralizes_of_fix_upper r hr
  · exact mem_centralizer_singleton_iff.mp (hAC ha)
  · intro v hv
    have hvB : v ∈ fixedSpace (binaryAction (F:=F)) B := by
      intro b
      exact elementary_fix_upper (hBE b.property) hv
    rw [←hfix] at hvB
    exact hvB ⟨a,ha⟩
omit [Finite F] in
private theorem coordinate_faithful : Function.Injective (binaryAction (F:=F)) := by
  intro g h he
  apply Natural.action_injective F
  apply LinearMap.ext
  intro v
  apply (Restricted.NaturalCoordinates.equiv F).injective
  have hg := LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' g) v
  have hh := LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' h) v
  exact hg.trans ((LinearMap.congr_fun he _).trans hh.symm)

omit [CharP F 2] [Algebra (ZMod 2) F] [Finite F] in
private theorem highest_le_long : (highestRoot (F:=F)) ≤ longRootLocal := by
  rintro _ ⟨r,rfl⟩
  exact rootA_mem_longRootLocal _

omit [CharP F 2] [Algebra (ZMod 2) F] in
private theorem highest_relIndex_long {n : ℕ} (hc : Nat.card F = 2^n) :
    (highestRoot (F:=F)).relIndex longRootLocal = 2^n := by
  have hh := relIndex_mul_card_of_le (highest_le_long (F:=F))
  rw [card_highestRoot,card_longRootLocal,hc,pow_two] at hh
  exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos n) hh

/-- Pure-long subgroups cannot satisfy the source A_k condition above n. -/
theorem not_family_of_le_longRootLocal {n k : ℕ} (hc : Nat.card F = 2^n) (hn : n < k)
    (A : Subgroup (Model F)) (hAL : A ≤ longRootLocal) :
    A ∉ fixedSpaceFamily (binaryAction (F:=F)) k := by
  intro hA
  let B := A ⊓ highestRoot
  have hi : B.relIndex A ≤ 2^n := by
    rw [show B = A ⊓ highestRoot from rfl,inf_relIndex_left]
    apply (relIndex_le_of_le_right hAL (by
      rw [highest_relIndex_long hc]; exact (Nat.two_pow_pos n).ne')).trans_eq
    exact highest_relIndex_long hc
  have hfix := hA.2.2 B inf_le_left (by
    have hh := Nat.log_mono_right (b:=2) hi
    rw [Nat.log_pow (by decide : 1<2)] at hh
    omega)
  have hAH : A ≤ highestRoot := by
    intro a ha
    obtain ⟨p,hp⟩ := hAL ha
    have hv : (Pi.single (3 : Fin 6) (1:F)) ∈ fixedSpace (binaryAction (F:=F)) B := by
      rintro ⟨b,hb⟩
      obtain ⟨t,rfl⟩ := hb.2
      change Restricted.NaturalCoordinates.action F (rootA t.toAdd) (Pi.single 3 1) = _
      ext i
      fin_cases i <;> simp
    rw [←hfix] at hv
    have he := hv ⟨a,ha⟩
    change Restricted.NaturalCoordinates.action F a (Pi.single 3 1) = _ at he
    have he0 := congrFun he 0
    rw [←hp] at he0
    have hz : p.toAdd.2 = 0 := by
      simpa [longRootHom,map_mul,Module.End.mul_apply] using he0
    refine ⟨Multiplicative.ofAdd p.toAdd.1,?_⟩
    rw [←hp]
    simp [longRootHom,hz,highestRootHom]
  have hr := parameter_le_rank_of_mem_fixedSpaceFamily _ coordinate_faithful hA
  have hh := card_le_of_le hAH
  rw [card_highestRoot,hc] at hh
  have hh' := Nat.log_mono_right (b:=2) hh
  rw [Nat.log_pow (by decide : 1<2)] at hh'
  change rank A ≤ n at hh'
  omega

/-- B.4.6(9): every A_k actor with k > n lies in an actual conjugate
of the A-B-C elementary subgroup, for every nonzero binary field degree. -/
theorem family_le_conjugate_elementary {n k : ℕ} (hc : Nat.card F = 2^n) (hn : n < k)
    (A : Subgroup (Model F)) (hA : A ∈ fixedSpaceFamily (binaryAction (F:=F)) k) :
    ∃ g : Model F, A ≤ (EvenTwoRank.elementary F).map (MulAut.conj g).toMonoidHom := by
  let := hA.2.1.2
  by_cases hs : ∃ b ∈ A, ShortRootProducts.IsShortRootElement b
  · obtain ⟨b,hb,r,hr,g,rfl⟩ := hs
    let B := A.map (MulAut.conj g⁻¹).toMonoidHom
    have hB : B ∈ fixedSpaceFamily (binaryAction (F:=F)) k :=
      fixedSpaceFamily_conjugationInvariant _ _ A hA g⁻¹
    have hm : rootC r ∈ B := by
      refine ⟨MulAut.conj g (rootC r),hb,?_⟩
      simp [MulAut.conj_apply,mul_assoc]
    have hBE := le_elementary_of_shortRoot hc hn B hB r hr hm
    refine ⟨g,?_⟩
    intro a ha
    refine ⟨MulAut.conj g⁻¹ a,hBE (mem_map_of_mem _ ha),?_⟩
    simp [MulAut.conj_apply,mul_assoc]
  · have hp : ∀ b ∈ A, b ≠ 1 → ShortRootProducts.IsLongRootElement b := by
      intro b hb hne
      rcases EvenInvolutionGeometry.involution_isRoot
        (elemPow_eq_one_of_isElementaryAbelian b hb) hne with ⟨g,r,hr,he⟩ | ⟨g,r,hr,he⟩
      · exact ⟨r,hr,g,he⟩
      · exact (hs ⟨b,hb,r,hr,g,he⟩).elim
    obtain ⟨g,hg⟩ := EvenInvolutionGeometry.PureLong.exists_map_le_longRootLocal A hA.2.1.2 hp
    exact (not_family_of_le_longRootLocal hc hn _ hg
      (fixedSpaceFamily_conjugationInvariant _ _ A hA g)).elim
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition
