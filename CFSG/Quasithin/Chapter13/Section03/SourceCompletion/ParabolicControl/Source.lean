module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ParabolicControl
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.HallSelection.OriginalSource
/-!
# The original unitary terminal actor from plane noncentrality

A compatible marking of the original Sylow flag constructs the literal
13.3.15(6) and 13.3.17(1) normalizer control. This discharges that premise,
and consequently the conjugate-module commutator premise, in the existing
F.9 closure, weak-closure and Hall–Cartan terminal actor construction.
The output retains the same original HStar subgroup and escaping prime actor.

The genuine earlier normal chosen-module marking, 13.3.14 movement and
strict rank bound remain source inputs. The terminal 4.4.3 odd-local control
is a separate earlier theorem; it is not replaced by a conclusion premise.
Source: Aschbacher–Smith 13.3.15–20, printed pp.894–896.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G]
/-- The original normal chosen-module action and the genuine 13.3.14
movement supply both 13.3.15(6) and 13.3.17(1), in the original groups. -/
theorem unitary_original_parabolic_control
    (D:ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
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
    (hVLT:D.V≤D.LT) (hred:IsPReduced 2 (D.V.subgroupOf D.LT))
    (hNL:normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (hfaith:D.L⊓centralizer (D.V:Set G)≤D.L.pCoreIn 2)
    (B:Subgroup G) (hBV:B≤D.V)
    (hTB:(D.T:Subgroup G)≤normalizer (B:Set G)) (hB:Nat.card B=4)
    (hHfull:D.H=normalizer (D.V₁:Set G)) (hm:⁅D.QH,B⁆≠⊥)
    (hTI:∀g∈normalizer (D.L:Set G),D.V⊓D.V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      D.V.map (MulAut.conj g).toMonoidHom=D.V) :
    centralizer (D.Vplus:Set G)≤normalizer (D.V:Set G) ∧
      D.H⊓normalizer (D.Vplus:Set G)≤normalizer (D.V:Set G) := by
  have hLTN:D.LT≤normalizer (D.V:Set G):=
    (normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal
  obtain ⟨rho,E,he,_,hd,hz,hp,hs⟩:=exists_unitary_flag_marking D.T D.L D.V₁ B D.Vplus
    (le_sup_left.trans hLTN) hNL e E0 he0 (le_sup_right.trans hLTN)
    hZV hBV hUV hTZ hTB hTU hZ hB hU
  have hm':⁅(normalizer (D.V₁:Set G)).pCoreIn 2,B⁆≠⊥:=by
    simpa only [ChapterF.Section09.Setup.QH,hHfull] using hm
  have hc:=unitary_flag_normalizer_control D.T D.L D.V₁ B D.Vplus rho E he hz hp hs
    hZV hBV hUV hTZ hTB hTL (le_sup_left.trans hLTN) hfaith hres hd hTI hm'
  have hcontrol:D.H⊓normalizer (D.Vplus:Set G)≤normalizer (D.V:Set G):=by
    simpa only [hHfull] using hc.2
  exact ⟨hc.1,hcontrol⟩

/-- The original terminal prime actor, with the local flag-control and
conjugate-module commutator conclusions both derived internally. -/
theorem unitary_escaping_prime_actor_of_plane_noncentrality
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
  have hcontrol:=(unitary_original_parabolic_control D e E0 he0 hUV hZV hTZ hTU hZ hU
    hres hTL hVLT hred hNL hfaith B hBV hTB hB hHfull hm hTI).2
  exact unitary_escaping_prime_actor_of_source D e E0 he0 hUV hZV hTZ hTU hZ hU hres hTL
    hcharL hVLT hred hsyl hcharH hcontrol hNL hfaith hu hout B hBV hTB hB hr hHfull hm
    hG hNT hTI

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
