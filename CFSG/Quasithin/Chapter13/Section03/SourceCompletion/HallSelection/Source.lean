module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.HallSelection
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.AboveTwo
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.LargeGeneration
/-!
# The original unitary terminal odd actor

For the original minimal outside subgroup H, identify the intrinsic unique
maximal subgroup with H∩N(L). The full original E.2.2 source dispatcher then
constructs the same Hall–Cartan witness for every case with n(H)>2. The
selected torus theorem produces an elementary prime-order actor centralizing
V and L/O₂(L), whose relative normalizer escapes N(L).

The last theorem chooses H itself inside the original point normalizer by
the proved weak-closure and E.3.35 argument. Thus no Hall model, component
case, normalizer escape or generation conclusion is an input. The earlier
4.4.3 unitary normalizer control is still needed to contradict this actor.

Source: Aschbacher–Smith 12.2.11(c), pp.798–799, and the terminal argument
of 13.3.16, pp.895–896. All module, flag and ambient maps are unchanged.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterB ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The original minimal outside member has exactly the original overlap as
its intrinsic maximal subgroup; no new maximal marking is selected. -/
theorem hstar_maximal_eq_overlap (T : Sylow 2 G) (M H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    minimalParabolicMax (T.subtype hH.1.1.2) hP = M.subgroupOf H := by
  let J := minimalParabolicMax (T.subtype hH.1.1.2) hP
  have hJ := minimalParabolicMax_spec (T.subtype hH.1.1.2) hP
  have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
    have hh := map_mono (f := H.subtype) hJ.2
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hJH : J.map H.subtype < H := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hJ.1.lt_top
    change J.map H.subtype < (⊤ : Subgroup H).map H.subtype at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hJM : J ≤ M.subgroupOf H := map_le_iff_le_comap.mp
    (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
  have hn : M.subgroupOf H ≠ ⊤ := fun he => hH.1.2 (subgroupOf_eq_top.mp he)
  exact ((hJ.1.le_iff.mp hJM).resolve_left hn).symm

/-- The full original E.2.2 classification supplies the actual large-prime
actor required by the unitary 12.2.11(c) terminal argument. All reflected
Cartan and escaping-normalizer premises are produced by the source model
classification, on this same H and its original Sylow. -/
theorem unitary_hstar_prime_actor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (L H U V : Subgroup G) [IsElementaryAbelian 2 V]
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hn : 2 < generationParameter H)
    (hLN : L ≤ normalizer (V : Set G)) (hNL : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ normalizer (L : Set G), V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hU : U ≠ ⊥) (hUV : U ≤ V) (hHU : H ≤ normalizer (U : Set G))
    (hres : pResidual 2 L = ⊤) (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (e : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer V L) v, E0 (automizerRepresentation V l v) =
      Atlas.G2.Natural.derivedAction F (e l) (E0 v)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧ Nat.card A = p ∧
      IsElementaryAbelian p A ∧ A ≤ H ⊓ normalizer (L : Set G) ∧
      A ≤ centralizer (V : Set G) ∧ ⁅A,L⁆ ≤ L.pCoreIn 2 ∧
      ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  have hP0 := Chapter3.HStar.minimalParabolic T hTM hH (Or.inl hNT)
  have hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ :=
    minimalParabolic_subtype T H hP0
  obtain ⟨n,_,hbound,d,hescape⟩ := MarkedModels.Inverted.source_intrinsic_escape_of_parameter_gt_two
    (Chapter3.sqtk_of_mem_H hG hH.1.1.1) (T.subtype hH.1.1.2) hP hn
  obtain ⟨p,A,hp,hp3,hAc,hAe,_,hAH,hAV,hAL,hAN⟩ := unitary_torus_prime_actor
    T L H U hH.1.1.2 d (hn.trans_le hbound) (hstar_maximal_eq_overlap T _ H hH hP)
    hescape hLN hNL hTN hTI hU hUV hHU hres hfaith e E0 he0
  exact ⟨p,A,hp,hp3,hAc,hAe,hAH,hAV,hAL,hAN⟩

/-- The original 13.3.16 module and flag construct both the minimal outside
group and its genuine escaping odd actor. The full E.2.2 dispatcher is
internal; only the separate earlier 4.4.3 normalizer control remains to
contradict this output. -/
theorem unitary_original_escaping_prime_actor
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
    (hcomm:∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥)
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
  obtain ⟨H,hH,hHD,hn⟩ := exists_large_generation_hstar_of_original_module D
    (normalizer (D.L:Set G)) e E0 he0 hUV hZV hTZ hTU hZ hU hres hTL hcharL hVLT
    hred hsyl hcharH hcontrol hNL hfaith hu hout hcomm B hBV hTB hB hr hHfull hm hG
  have hLTN:D.LT≤normalizer (D.V:Set G):=
    (normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal
  have hZn:D.V₁≠⊥:=D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  refine ⟨H,hH,hHD,hn,?_⟩
  exact unitary_hstar_prime_actor hG D.T D.L H D.V₁ D.V hH hTL hNT hn
    (le_sup_left.trans hLTN) hNL (le_sup_right.trans hLTN) hTI hZn hZV
    (hHD.trans hHfull.le) hres hfaith e E0 he0

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
