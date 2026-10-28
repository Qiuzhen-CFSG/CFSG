module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.HallSelection.Source
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalIntersections
/-!
# The original unitary odd actor after the pair-geometry reduction

Apply the completed original unitary intersection theorem to discharge the
commutator input of the F.9 closure and weak-closure argument. The original
point/three-space bound suffices: the actual E.6.1 setup, compatible three-space
marking and its centralizer containment are all constructed. The source
Hall–Cartan dispatcher then supplies the literal escaping prime-order actor.

The remaining terminal theorem is the genuine earlier 4.4.3 unitary odd-local
control statement. No instance of that conclusion is assumed here.
Source: Aschbacher–Smith 13.3.16–20, pp.894–896, and 12.2.11(c), pp.798–799.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G]
/-- The original unitary terminal actor with the commutator obstruction
discharged from the genuine point/three-space normalizer control. -/
theorem unitary_escaping_prime_actor_of_source
    (D:ChapterF.Section09.Setup G)
    [IsElementaryAbelian 2 D.V]
    (e:inducedAutomizer D.V D.L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0:Additive D.V≃ₗ[F]Atlas.G2.Natural.Space F)
    (he0:∀(l:inducedAutomizer D.V D.L) v,E0 (automizerRepresentation D.V l v)=
      Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV:D.Vplus≤D.V) (hZV:D.V₁≤D.V)
    (hTZ:(D.T:Subgroup G)≤normalizer (D.V₁:Set G))
    (hTU:(D.T:Subgroup G)≤normalizer (D.Vplus:Set G))
    (hZ:Nat.card D.V₁=2) (hU:Nat.card D.Vplus=8)
    (hres:pResidual 2 D.L=⊤)
    (hTL:(D.T:Subgroup G)≤normalizer (D.L:Set G))
    (hcharL:generalizedFitting D.L=pCore 2 D.L)
    (hVLT:D.V≤D.LT) (hred:IsPReduced 2 (D.V.subgroupOf D.LT))
    (hsyl:(D.T:Subgroup G)⊓centralizer (D.V:Set G)=D.LT.pCoreIn 2)
    (hcharH:generalizedFitting D.H=pCore 2 D.H)
    (hcontrol:D.H⊓normalizer (D.Vplus:Set G)≤normalizer (D.V:Set G))
    (hNL:normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (hfaith:D.L⊓centralizer (D.V:Set G)≤D.L.pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→D.LT≤N→N=normalizer (D.L:Set G))
    (hout:¬D.H≤normalizer (D.L:Set G))
    (B:Subgroup G) (hBV:B≤D.V)
    (hTB:(D.T:Subgroup G)≤normalizer (B:Set G)) (hB:Nat.card B=4)
    (hr:(3:ℕ∞)<globalR D.V) (hHfull:D.H=normalizer (D.V₁:Set G))
    (hm:⁅D.QH,B⁆≠⊥)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hNT:normalizer (D.T:Set G)≤normalizer (D.L:Set G))
    (hTI:∀g∈normalizer (D.L:Set G),D.V⊓D.V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      D.V.map (MulAut.conj g).toMonoidHom=D.V) :
    ∃ H ∈ Chapter3.HStar (D.T:Subgroup G) (normalizer (D.L:Set G)),
      H≤D.H ∧ 2<generationParameter H ∧
      ∃ (p:ℕ) (A:Subgroup G),p.Prime ∧ 3<p ∧ Nat.card A=p ∧
        IsElementaryAbelian p A ∧ A≤H⊓normalizer (D.L:Set G) ∧
        A≤centralizer (D.V:Set G) ∧ ⁅A,D.L⁆≤D.L.pCoreIn 2 ∧
        ¬H⊓normalizer (A:Set G)≤normalizer (D.L:Set G) := by
  have hcomm:=unitary_intersection_commutator_eq_bot_of_source D hG e E0 he0 hUV hZV
    hTZ hTU hZ hU hTL hVLT hred hsyl hcontrol hNL hu B hBV hTB hB hHfull hTI
  exact unitary_original_escaping_prime_actor D e E0 he0 hUV hZV hTZ hTU hZ hU
    hres hTL hcharL hVLT hred hsyl hcharH hcontrol hNL hfaith hu hout
    (fun g _ hc=>hcomm g hc) B hBV hTB hB hr hHfull hm hG hNT hTI
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
