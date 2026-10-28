module
public import Theory.GroupAction.PerfectSectionDegreeTwo
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorFactorSection
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointResidual
public import CFSG.Quasithin.Chapter1.Section03.FrattiniShape

/-!
# The final small-action contradiction at a tensor point

Once the original Xi subgroup is normalized by L₀, its odd quotient has
Frattini quotient of order p². The opposite component factor commutes with
L modulo O₂(L), so the perfect section-action obstruction kills the action
of L on the odd quotient. The actual T_v orbit generation then kills L₀.
This contradicts X = [X,L_N] for the original tensor point residual L_N.

The factor-swapping element and the equality of the T_v orbit with L₀ are
explicit geometric inputs. The preceding Xi construction and conjugate
rigidity supply Xi membership, normalization, and the commutator equality.
No point-normality or action-triviality premise is substituted for them.
Source: Aschbacher--Smith, proof of 9.4.1, printed p.736.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

omit [Finite G] in
private theorem quotient_kernel_le_section (X : Subgroup G) :
    (((quotientAut (pCore 2 X)).comp X.normalizerMonoidHom).ker).map
      (normalizer (X : Set G)).subtype ≤ sectionCentralizer X := by
  let a := (quotientAut (pCore 2 X)).comp X.normalizerMonoidHom
  let K := a.ker.map (normalizer (X : Set G)).subtype
  apply (le_sectionCentralizer_iff K X).mpr
  refine ⟨map_subtype_le _, commutator_le.mpr ?_⟩
  rintro n ⟨b,hb,rfl⟩ y hy
  let x : X := ⟨y,hy⟩
  have hf := DFunLike.congr_fun (show a b = 1 from hb) (QuotientGroup.mk' (pCore 2 X) x)
  change quotientAut (pCore 2 X) (X.normalizerMonoidHom b)
    (QuotientGroup.mk' (pCore 2 X) x) = QuotientGroup.mk' (pCore 2 X) x at hf
  rw [quotientAut_apply_mk] at hf
  have hk : X.normalizerMonoidHom b x * x⁻¹ ∈ pCore 2 X := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom b x * x⁻¹) = 1
    rw [map_mul,map_inv,hf,mul_inv_cancel]
  exact mem_map_of_mem X.subtype hk

include m in
/-- The original component orbit centralizes the odd Xi quotient. The factor
swap and its orbit generation are the precise remaining point geometry. -/
theorem tensorPoint_Xi_orbit_le_sectionCentralizer
    {R X : Subgroup G} (hX : Chapter1.XiMember R X)
    (hNX : localOrbit T L ≤ normalizer (X : Set G))
    (t : G) (ht : t ∈ R) (htT : t ∈ (T : Subgroup G))
    (htL : t ∉ normalizer (L : Set G))
    (hgen : componentOrbit L R = localOrbit T L) :
    localOrbit T L ≤ sectionCentralizer X := by
  obtain ⟨p,hp,ho,hq⟩ := hX.odd_quotient
  let : Fact p.Prime := ⟨hp⟩
  let N := normalizer (X : Set G)
  let a : N →* MulAut (Chapter1.XiQuotient X) :=
    (quotientAut (pCore 2 X)).comp X.normalizerMonoidHom
  have hLN : L ≤ N := (le_componentOrbit L (T : Subgroup G)).trans hNX
  let A := L.subgroupOf N
  let tN : N := ⟨t,hX.invariant ht⟩
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hLN).symm.surjective
  have hmA : A.map N.subtype = L := map_subgroupOf_eq_of_le hLN
  have hmB : (A.map (MulAut.conj tN).toMonoidHom).map N.subtype =
      L.map (MulAut.conj t).toMonoidHom := by
    rw [map_map,show N.subtype.comp (MulAut.conj tN).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp N.subtype from rfl,← map_map,hmA]
  have hc : ⁅A.map (MulAut.conj tN).toMonoidHom,A⁆ ≤ A.pCoreIn 2 := by
    apply (map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_commutator,map_pCoreIn_of_injective 2 _ _ N.subtype_injective,hmA,hmB]
    exact (le_sectionCentralizer_iff _ _).mp
      (m.conjugate_factor_le_sectionCentralizer htT htL) |>.2
  have ha := Subgroup.perfect_conjugate_section_frattini_two_trivial ho A tN
    hq.isPGroup hq.frattini_card.le a hc
  let K := a.ker.map N.subtype
  have hAK : A ≤ a.ker := by
    intro x hx
    exact DFunLike.congr_fun ha (⟨x,hx⟩ : A)
  have hLK : L ≤ K := hmA ▸ map_mono hAK
  have hNK : N ≤ normalizer (K : Set G) := by
    have hh := Subgroup.le_normalizer_map (H := a.ker) N.subtype
    simpa only [Subgroup.normalizer_eq_top,← MonoidHom.range_eq_map,Subgroup.range_subtype] using hh
  have hOK : localOrbit T L ≤ K := by
    rw [← hgen]
    exact iSup_conjugates_le_of_le_normalizer L R K hLK (hX.invariant.trans hNK)
  exact hOK.trans (quotient_kernel_le_section X)

/-- The degree-two action step contradicts the actual point-residual
commutator equality in the final paragraph of 9.4.1. -/
theorem tensorPoint_Xi_action_contradiction
    {R X : Subgroup G} (hX : Chapter1.XiMember R X)
    (hNX : localOrbit T L ≤ normalizer (X : Set G))
    (t : G) (ht : t ∈ R) (htT : t ∈ (T : Subgroup G))
    (htL : t ∉ normalizer (L : Set G))
    (hgen : componentOrbit L R = localOrbit T L)
    (v : D.fullModule) (hm : ⁅X,m.tensorPointResidual v⁆ = X) : False := by
  have hs := m.tensorPoint_Xi_orbit_le_sectionCentralizer hX hNX t ht htT htL hgen
  have hc : ⁅X,localOrbit T L⁆ ≤ X.pCoreIn 2 := by
    rw [commutator_comm]
    exact (le_sectionCentralizer_iff _ _).mp hs |>.2
  have hXcore : X ≤ X.pCoreIn 2 := by
    calc
      X = ⁅X,m.tensorPointResidual v⁆ := hm.symm
      _ ≤ X.pCoreIn 2 :=
        (commutator_mono le_rfl (m.tensorPointResidual_le_orbit v)).trans hc
  have hall (x : X) : x ∈ pCore 2 X := by
    obtain ⟨y,hy,he⟩ := hXcore x.property
    exact (show y = x from Subtype.ext he) ▸ hy
  have hqone (q : Chapter1.XiQuotient X) : q = 1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
    exact (QuotientGroup.eq_one_iff _).mpr (hall x)
  let : Subsingleton (Chapter1.XiQuotient X) :=
    ⟨fun a b => (hqone a).trans (hqone b).symm⟩
  have hcq : Nat.card (Chapter1.XiQuotient X) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
  obtain ⟨p,hp,_,hq⟩ := hX.odd_quotient
  have hne := hq.one_lt_card hp
  omega

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
