module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalContainment
public import CFSG.Quasithin.Chapter13.Section03.LocalSteps
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
/-!
# The actual large-generation outside member

The original unitary natural action and commuting-intersection theorem force
all escape indices above two. The genuine E.3.35 source implication therefore
puts every small-generation H(T) member in M. Finite descent inside the original
escaping involution centralizer selects an H*(T,M) member, whose generation
parameter must exceed two. The final consumer uses the original F.9 setup
and its already proved module, flag and weak-closure construction.

Source: Aschbacher–Smith 13.3.19–20 and the final paragraph of 13.3.16,
printed pp.895–896. This selection asserts no odd-local control theorem.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE
variable {G : Type*} [Group G] [Finite G]
/-- The actual escaping point centralizer contains a minimal outside member
of generation parameter greater than two. Small-generation containment is
constructed from the original module, rather than postulated. -/
theorem exists_unitary_large_generation_hstar
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (L V M : Subgroup G) [IsElementaryAbelian 2 V]
    (hne : V ≠ ⊥) (hVT : V ≤ T) (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hLN : L ≤ normalizer (V : Set G))
    (hsyl : (T : Subgroup G) ⊓ centralizer (V : Set G) = (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hinter : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hr : (3 : ℕ∞) < globalR V)
    (I : Subgroup (Automizer V)) [I.Normal]
    (e : I ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E : Additive V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (he : ∀ (l : I) v, E (automizerRepresentation V l v) =
      Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E v))
    (z : G) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hout : ¬ centralizer ({z} : Set G) ≤ M) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) M,
      H ≤ centralizer ({z} : Set G) ∧ 2 < generationParameter H := by
  obtain ⟨H,hH,hHC⟩ := exists_HStar_le_involution_centralizer (T : Subgroup G) M z hz hTz hout
  refine ⟨H,hH,hHC,?_⟩
  by_contra hn
  exact hH.1.2 (small_generation_overgroup_le_of_unitary_bounds T L V M H
    hne hVT hTN hLN hsyl hu (Chapter3.sqtk_of_mem_H hG hH.1.1.1) hH.1.1.2
    (unitary_globalW_gt_two hTN hinter hr I e E he) hr (by omega))
open Atlas.G2.Natural.BinaryPointFlag
/-- Source 13.3.16 chooses the minimal outside group inside the actual
point normalizer. Its large generation parameter follows from the complete
original weak-closure and E.3.35 consumer, with no containment callback. -/
theorem exists_large_generation_hstar_of_original_module
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
    (hm:⁅D.QH,B⁆≠⊥)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    : ∃ H ∈ Chapter3.HStar (D.T : Subgroup G) M,
      H ≤ D.H ∧ 2 < generationParameter H := by
  have hZne : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  obtain ⟨z,hzne⟩ := ne_bot_iff_exists_ne_one.mp hZne
  have hz1 : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  have hzo : orderOf (z : G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z : G) (hZV z.property)) hz1
  have hC : centralizer ({(z : G)} : Set G) = D.H :=
    (point_normalizer_eq_generator_centralizer D.V₁ hZ z z.property hz1).trans hHfull.symm
  have hTz : (D.T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) := by
    rw [hC,hHfull]
    exact hTZ
  obtain ⟨H,hH,hHC⟩ := exists_HStar_le_involution_centralizer (D.T : Subgroup G) M z hzo hTz
    (hC.symm ▸ hout)
  refine ⟨H,hH,hC ▸ hHC,?_⟩
  by_contra hn
  exact hH.1.2 (unitary_small_generation_overgroup_le_of_original_module D M e E0 he0 hUV hZV
    hTZ hTU hZ hU hres hTL hcharL hVLT hred hsyl hcharH hcontrol hNL hfaith hu hout
    hcomm B hBV hTB hB hr hHfull hm hG H hH.1.1 (by omega))

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
