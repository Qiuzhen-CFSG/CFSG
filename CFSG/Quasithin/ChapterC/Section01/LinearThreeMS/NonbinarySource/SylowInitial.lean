module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralCore
public import Theory.GroupTheory.TwoFixedLinesIrreducible

/-!
# The actual Sylow omega on the initial nonbinary MS module

Every central involution of S lies in O₂(KR), by self-centrality of that
core, and hence lies in Ω₁(Z(O₂(KR))). The initial moved/fixed splitting
is preserved by S. Uniqueness of its two factors therefore splits the
actual Ω₁(Z(S)) into the S-fixed part of the initial moved group and
Ω₁(Z(KR)). In particular its component centralizer and its whole join
centralizer are computed on that initial S-fixed subgroup.

A nontrivial normal two-group has nonzero S-fixed points. Applied to the
initial moved factor, whose K-fixed subgroup is trivial, this excludes
centrality of Ω₁(Z(S)) for every nonbinary field, including field four.
None of these results assumes abelianity or recognition of the whole msQ.
The radical inequality now reduces to the already classified initial
module; evaluating that comparison and recognizing the whole central and
Frattini sections are still required for C.1.34.

The original Chapter4 and Chapter11 applications retain their literal
radicals, Sylows, field sizes and quotient markings.
Source: Aschbacher--Smith C.1.31--34, printed pp.135--137, and the original
4.3.8--10 and11.1.5, pp.616--617,765--766.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SylowInitial
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "N" => Subgroup.pCoreIn 2 (K ⊔ R : Subgroup G)
local notation "E" => initialOmega K R
local notation "U" => initialMoved K R

omit [Finite G] in
private theorem omega_le_core : E ≤ N := by
  rw [initialOmega_eq]
  exact fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).1

omit [Finite G] in
private theorem centralizer_join (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) =
      centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm (le_inf
    (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
    (centralizer_le (show B ≤ A ⊔ B from le_sup_right)))
  apply le_centralizer_iff.mp
  exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)

include h in
/-- Central involutions of the actual Sylow lie in the original initial layer. -/
theorem sylowOmega_le_initialOmega {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) : SourceInterface.omegaCenterIn S ≤ E := by
  have hSJ : S ≤ J := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hNS : N ≤ S := by
    obtain ⟨P,hP⟩ := hS
    exact hP ▸ pCoreIn_le_sylow J P
  intro z hz
  obtain ⟨hzS,hzc,hze⟩ := (mem_omegaCenterIn_iff S z).mp hz
  have hzN : z ∈ N := by
    apply mem_map_of_mem (J).subtype (x := ⟨z,hSJ hzS⟩)
    apply core_selfCentralizing h
    intro d hd
    exact Subtype.ext (hzc d (hNS (mem_map_of_mem (J).subtype hd)))
  rw [initialOmega_eq]
  exact (mem_omegaCenterIn_iff N z).mpr ⟨hzN,centralizer_le hNS hzc,hze⟩

include h in
/-- The Sylow's central omega is the actual fixed subgroup of the initial layer. -/
theorem sylowOmega_eq_initial_fixed {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) :
    SourceInterface.omegaCenterIn S = E ⊓ centralizer (S : Set G) := by
  have hNS : N ≤ S := by
    obtain ⟨P,hP⟩ := hS
    exact hP ▸ pCoreIn_le_sylow J P
  apply le_antisymm
  · exact le_inf (sylowOmega_le_initialOmega h hS)
      (fun z hz => ((mem_omegaCenterIn_iff S z).mp hz).2.1)
  · rintro z ⟨hz,hzc⟩
    rw [initialOmega_eq] at hz
    obtain ⟨hzN,_,hze⟩ := (mem_omegaCenterIn_iff N z).mp hz
    exact (mem_omegaCenterIn_iff S z).mpr ⟨hNS hzN,hzc,hze⟩

omit [Finite G] in
private theorem join_normalizes_omega : J ≤ normalizer (E : Set G) := by
  change J ≤ normalizer ((centralOmegaLayer K R).map (J).subtype : Set G)
  have hh := (centralOmegaLayer K R).le_normalizer_map (J).subtype
  simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,(J).range_subtype] using hh

include h hn in
/-- The original join preserves the moved factor of its initial layer. -/
theorem join_normalizes_moved : J ≤ normalizer (U : Set G) := by
  have hJK := (normal_subgroupOf_iff_le_normalizer (show K ≤ J from le_sup_left)).mp
    (component_normal h hn)
  intro j hj
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [initialMoved,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (join_normalizes_omega (K := K) (R := R) hj),
    mem_normalizer_iff_map_conj_eq.mp (hJK hj)]

variable [CharP F 2]
include h hn

private theorem moved_fixed_eq_bot : U ⊓ centralizer (K : Set G) = ⊥ := by
  apply bot_unique
  exact (le_inf inf_le_left (le_inf (inf_le_left.trans initialMoved_le_omega)
    inf_le_right)).trans_eq (initialMoved_split h hn).2

private theorem sylow_factorization {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) {z : G}
    (hz : z ∈ SourceInterface.omegaCenterIn S) :
    ∃ u ∈ U ⊓ centralizer (S : Set G),
      ∃ c ∈ SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G), u*c=z := by
  let C := E ⊓ centralizer (K : Set G)
  have hCU : C ≤ normalizer (U : Set G) := by
    apply le_trans _ (centralizer_le_normalizer (U : Set G))
    exact (le_centralizer_iff.mp initialMoved_centralizes_joinCore).trans'
      (inf_le_left.trans omega_le_core)
  have hzEC : z ∈ U ⊔ C := (initialMoved_split h hn).1.symm ▸
    (sylowOmega_le_initialOmega h hS hz)
  have hzprod : z ∈ (U : Set G) * (C : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left U C hCU]
    exact hzEC
  obtain ⟨u,hu,c,hc,he⟩ := Set.mem_mul.mp hzprod
  have hSJ : S ≤ J := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hJK := (normal_subgroupOf_iff_le_normalizer (show K ≤ J from le_sup_left)).mp
    (component_normal h hn)
  have huS : u ∈ centralizer (S : Set G) := by
    intro s hs
    let u' := s*u*s⁻¹
    let c' := s*c*s⁻¹
    have hu' : u' ∈ U := (join_normalizes_moved h hn (hSJ hs) u).mp hu
    have hc' : c' ∈ centralizer (K : Set G) :=
      (normalizer_le_normalizer_centralizer K (hJK (hSJ hs)) c).mp hc.2
    have hp : u'*c' = u*c := by
      calc
        u'*c' = s*(u*c)*s⁻¹ := by dsimp [u',c']; group
        _ = s*z*s⁻¹ := by rw [he]
        _ = z := by rw [((mem_omegaCenterIn_iff S z).mp hz).2.1 s hs,mul_inv_cancel_right]
        _ = u*c := he.symm
    have hd : u⁻¹*u' = c*c'⁻¹ := by
      calc
        u⁻¹*u' = u⁻¹*(u'*c')*c'⁻¹ := by group
        _ = u⁻¹*(u*c)*c'⁻¹ := by rw [hp]
        _ = c*c'⁻¹ := by group
    have h1 : u⁻¹*u' = 1 := by
      apply (moved_fixed_eq_bot h hn).le
      refine ⟨(U).mul_mem ((U).inv_mem hu) hu',?_⟩
      rw [hd]
      exact (centralizer _).mul_mem hc.2 ((centralizer _).inv_mem hc')
    exact mul_inv_eq_iff_eq_mul.mp ((inv_mul_eq_one.mp h1).symm : u' = u)
  have huZ : u ∈ SourceInterface.omegaCenterIn S := by
    rw [sylowOmega_eq_initial_fixed h hS]
    exact ⟨initialMoved_le_omega hu,huS⟩
  have hcZ : c ∈ SourceInterface.omegaCenterIn S := by
    have hh := (SourceInterface.omegaCenterIn S).mul_mem
      ((SourceInterface.omegaCenterIn S).inv_mem huZ) hz
    rwa [←he,inv_mul_cancel_left] at hh
  exact ⟨u,⟨hu,huS⟩,c,⟨hcZ,hc.2⟩,he⟩

/-- The actual Sylow omega splits over the already classified initial moved
factor, regardless of the structure or abelianity of the whole MS core. -/
theorem sylowOmega_split {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) :
    SourceInterface.omegaCenterIn S =
      (U ⊓ centralizer (S : Set G)) ⊔
        (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G)) ∧
    (U ⊓ centralizer (S : Set G)) ⊓
      (SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G)) = ⊥ := by
  constructor
  · apply le_antisymm
    · intro z hz
      obtain ⟨u,hu,c,hc,rfl⟩ := sylow_factorization h hn hS hz
      exact Subgroup.mul_mem_sup hu hc
    · apply sup_le _ inf_le_left
      rw [sylowOmega_eq_initial_fixed h hS]
      exact inf_le_inf_right _ initialMoved_le_omega
  · apply bot_unique
    exact (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_right)).trans_eq (moved_fixed_eq_bot h hn)

/-- The component centralizer of the actual Sylow omega is computed entirely
on the Sylow-fixed vectors of the initial moved factor. -/
theorem component_centralizer {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) :
    K ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      K ⊓ centralizer ((U ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := by
  rw [(sylowOmega_split h hn hS).1,centralizer_join]
  apply le_antisymm
  · exact inf_le_inf_left _ inf_le_left
  · rintro k ⟨hk,hku⟩
    exact ⟨hk,hku,fun c hc => (hc.2 k hk).symm⟩

/-- The literal whole Sylow-omega centralizer is a product with the original
radical. No whole-core section recognition is required. -/
theorem join_centralizer {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      (K ⊓ centralizer ((U ⊓ centralizer (S : Set G) : Subgroup G) : Set G)) ⊔ R := by
  have hRC : R ≤ centralizer (SourceInterface.omegaCenterIn S : Set G) := by
    intro r hr z hz
    exact (((mem_omegaCenterIn_iff S z).mp hz).2.1 r (hRS hr)).symm
  apply le_antisymm
  · rintro x ⟨hx,hxc⟩
    obtain ⟨k,hk,r,hr,rfl⟩ := product h hn x hx
    have hkc : k ∈ centralizer (SourceInterface.omegaCenterIn S : Set G) := by
      have hh := (centralizer _).mul_mem hxc ((centralizer _).inv_mem (hRC hr))
      simpa only [mul_inv_cancel_right] using hh
    exact Subgroup.mul_mem_sup ((component_centralizer h hn hS).le ⟨hk,hkc⟩) hr
  · apply sup_le
    · intro k hk
      exact ⟨mem_sup_left hk.1,((component_centralizer h hn hS).ge hk).2⟩
    · exact le_inf le_sup_right hRC

/-- The radical inequality is exactly the comparison on the classified
initial moved module, with the actual Sylow and original radical unchanged. -/
theorem notCentralizerCore_iff {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    MSNotCentralizerCore K R S ↔ R ≠
      ((K ⊓ centralizer ((U ⊓ centralizer (S : Set G) : Subgroup G) : Set G)) ⊔ R).pCoreIn 2 := by
  unfold MSNotCentralizerCore
  rw [join_centralizer h hn hS hRS]


omit [CharP F 2] in
private theorem moved_ne_bot : U ≠ ⊥ := by
  intro hu
  have hc : K ≤ centralizer (E : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hu)
  apply component_not_le_centralOmegaKernel h hn
  intro k hk v hv
  exact Subtype.ext (hc hk v (mem_map_of_mem _ hv))

omit [CharP F 2] in
/-- The actual Sylow fixes a nonzero vector in the initial moved factor. -/
theorem moved_sylow_fixed_ne_bot {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) : U ⊓ centralizer (S : Set G) ≠ ⊥ := by
  have hSp : IsPGroup 2 S := by
    obtain ⟨P,hP⟩ := hS
    rw [←hP]
    exact P.isPGroup'.map (J).subtype
  exact inf_centralizer_ne_bot_of_pGroups S U hSp
    ((pCore_isPGroup.map (J).subtype).to_le
      (initialMoved_le_msQ.trans msQ_le_joinCore))
    (((Chapter1.isSylowIn_iff.mp hS).2.1).trans (join_normalizes_moved h hn))
    (moved_ne_bot h hn)

/-- At every nonbinary field, the central omega of the actual Sylow moves K.
This excludes C.1.34(5)'s central-omega clause before whole-core recognition. -/
theorem sylowOmega_not_centralizes_component {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) :
    ¬ SourceInterface.omegaCenterIn S ≤ centralizer (K : Set G) := by
  intro hc
  apply moved_sylow_fixed_ne_bot h hn hS
  apply bot_unique
  have hWZ : U ⊓ centralizer (S : Set G) ≤ SourceInterface.omegaCenterIn S := by
    rw [sylowOmega_eq_initial_fixed h hS]
    exact inf_le_inf_right _ initialMoved_le_omega
  exact (le_inf inf_le_left (hWZ.trans hc)).trans_eq (moved_fixed_eq_bot h hn)

/-- The actual Sylow omega cannot be central in KR at a nonbinary field. -/
theorem sylowOmega_not_central {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) :
    ¬ SourceInterface.omegaCenterIn S ≤ SourceInterface.centerIn J := by
  intro hc
  apply sylowOmega_not_centralizes_component h hn hS
  intro z hz k hk
  obtain ⟨z',hz',rfl⟩ := hc hz
  exact congrArg (J).subtype ((mem_center_iff.mp hz') ⟨k,mem_sup_left hk⟩)

omit hn [CharP F 2] in
/-- The component-fixed factor in the Sylow omega is exactly the central
omega of KR. This concerns this Sylow factor, not all of C_Q(K). -/
theorem sylow_fixed_factor {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    SourceInterface.omegaCenterIn S ⊓ centralizer (K : Set G) =
      SourceInterface.omegaCenterIn J := by
  have hSJ : S ≤ J := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hNS : N ≤ S := by
    obtain ⟨P,hP⟩ := hS
    exact hP ▸ pCoreIn_le_sylow J P
  apply le_antisymm
  · rintro z ⟨hz,hzK⟩
    obtain ⟨hzS,hzc,hze⟩ := (mem_omegaCenterIn_iff S z).mp hz
    apply (mem_omegaCenterIn_iff J z).mpr
    refine ⟨hSJ hzS,?_,hze⟩
    rw [centralizer_join]
    exact ⟨hzK,centralizer_le hRS hzc⟩
  · intro z hz
    obtain ⟨hzJ,hzc,hze⟩ := (mem_omegaCenterIn_iff J z).mp hz
    have hzN : z ∈ N := by
      apply mem_map_of_mem (J).subtype (x := ⟨z,hzJ⟩)
      apply core_selfCentralizing h
      intro x hx
      exact Subtype.ext (hzc x x.property)
    exact ⟨(mem_omegaCenterIn_iff S z).mpr
      ⟨hNS hzN,centralizer_le hSJ hzc,hze⟩,centralizer_le (show K ≤ J from le_sup_left) hzc⟩

/-- The canonical direct product decomposition of the actual Sylow omega. -/
theorem sylowOmega_split_center {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    SourceInterface.omegaCenterIn S =
      (U ⊓ centralizer (S : Set G)) ⊔ SourceInterface.omegaCenterIn J ∧
    (U ⊓ centralizer (S : Set G)) ⊓ SourceInterface.omegaCenterIn J = ⊥ := by
  have hs := sylowOmega_split h hn hS
  rwa [sylow_fixed_factor h hS hRS] at hs

/-- Even in the nonabelian core rows, the whole join centralizer is the
pointwise fixer of the actual initial Sylow-fixed subgroup. -/
theorem join_centralizer_initial {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      J ⊓ centralizer ((U ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := by
  rw [(sylowOmega_split_center h hn hS hRS).1,centralizer_join]
  apply le_antisymm (inf_le_inf_left _ inf_le_left)
  rintro j ⟨hj,hjU⟩
  exact ⟨hj,hjU,fun z hz => (((mem_omegaCenterIn_iff J z).mp hz).2.1 j hj).symm⟩

/-- The Sylow-omega centralizer is proper in KR at every nonbinary field. -/
theorem join_centralizer_lt {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) :
    J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) < J := by
  apply lt_of_le_of_ne inf_le_left
  intro he
  apply sylowOmega_not_centralizes_component h hn hS
  apply le_centralizer_iff.mp
  have hKJ : K ≤ J := le_sup_left
  exact hKJ.trans (he.symm ▸ inf_le_right)

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SylowInitial
