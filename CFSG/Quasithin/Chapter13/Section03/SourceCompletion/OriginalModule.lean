module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.MarkedAction

/-!
# The unitary point closure from the original module and chosen flag

The source normal component action determines a full binary G₂ embedding.
One model conjugation marks the actual Sylow, and uniqueness identifies
all three originally chosen invariant flag subgroups in that same frame.
The point-source consumer then proves the closure abelian, constructing
all F.9, point-parabolic, plane-residual, hyperplane and cross-action data.

This removes every coordinate-position and Sylow-image assumption. The
original natural module and the earlier ambient 12.2/13.3.17 conclusions
are retained explicitly for their source producers; the full U₃(3)
exclusion still also needs 13.3.19–20's terminal earlier implications.

Source: Aschbacher–Smith Notation13.3.3 and Lemma13.3.18, pp.885,894–895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G]

/-- The original abelian-closure consumer, with F.9 applicability and all
subsequent point/hyperplane/cross-action premises discharged in one proof. -/
theorem unitary_closure_abelian_of_original_module
    (D:ChapterF.Section09.Setup G) (M:Subgroup G)
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
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→D.LT≤N→N=M)
    (hout:¬D.H≤M)
    (hcomm:∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (B:Subgroup G) (hBV:B≤D.V)
    (hTB:(D.T:Subgroup G)≤normalizer (B:Set G)) (hB:Nat.card B=4)
    (hr:(3:ℕ∞)<globalR D.V) (hHfull:D.H=normalizer (D.V₁:Set G))
    (hm:⁅D.QH,B⁆≠⊥) : IsMulCommutative D.VH := by
  have hTN:(D.T:Subgroup G)≤normalizer (D.V:Set G):=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal)
  have hLN:D.L≤normalizer (D.V:Set G):=
    le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal)
  obtain ⟨rho,E,he,ht,hd,hz,hp,hs⟩:=exists_unitary_flag_marking D.T D.L D.V₁ B D.Vplus
    hLN hNL e E0 he0 hTN hZV hBV hUV hTZ hTB hTU hZ hB hU
  exact unitary_closure_abelian_of_source_action D M rho E he hs hz hUV hZV ht hd
    hres hTL hcharL hVLT hred hsyl hcharH hcontrol hNL hfaith hu hout hcomm B hBV hp hr hHfull hm

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
