module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponent
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupComponent
public import Theory.SpecificGroups.PSL2.TwentyFiveCartanNormalizer
public import Theory.GroupTheory.PResidual.NormalizerCore
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.OrbitSource
public import Theory.GroupAction.CardFourCubic.Conjugation

/-!
# Cartan normalization in the PSL₂(25) tensor overcomponent branch

Let K be the literal old residual O²(H), where H is the original H-star
member. In the PSL₂(25) row of the component containing K inside N_G(V₁),
the extended Cartan normalizes K. The larger component's two-core lies in
T and therefore normalizes K. Its actual quotient action has order at most
three, accounted for by the specified diagonal cubic inside K.

Irreducibility on V₁ and the original nontrivial H-fixed central element
then force K to centralize V₁. The final consumer supplies precisely this
centralization to the source9.3.5 commutator obstruction. The other source
9.3.1 container rows and the nonnormalizing FF branch remain separate.

Source: Aschbacher–Smith, combined manuscript of1 March2004,
Proposition9.3.1 and Lemma9.3.5, printed pp.732–733.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

omit [Finite G] in
/-- The first reduction in9.3.1: an irreducible normalizing actor propagates
the original fixed central element to the whole tensor line. -/
theorem source_hstar_residual_centralizes_irreducible_line
    (H U A : Subgroup G)
    (hAU : A ≤ normalizer (U : Set G))
    (hirr : ∀ N : Subgroup G, N ≤ U → A ≤ normalizer (N : Set G) →
      N = ⊥ ∨ N = U)
    (hAK : A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (z : G) (hz : z ≠ 1) (hzU : z ∈ U)
    (hzH : ∀ h ∈ H, h * z = z * h) :
    (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) := by
  let K := (pResidual 2 H).map H.subtype
  have hn : A ≤ normalizer (U ⊓ centralizer (K : Set G) : Set G) :=
    (le_inf hAU (hAK.trans (normalizer_le_normalizer_centralizer K))).trans
      inf_normalizer_le_normalizer_inf
  have hzC : z ∈ U ⊓ centralizer (K : Set G) :=
    ⟨hzU,fun k hk => hzH k (map_subtype_le _ hk)⟩
  have he : U ⊓ centralizer (K : Set G) = U :=
    (hirr _ inf_le_left hn).resolve_left (fun he => hz (mem_bot.mp (he ▸ hzC)))
  exact le_centralizer_iff.mp (he ▸ inf_le_right)

/-- Source9.3.1's actual old residual is normalized in the PSL₂(25)
overcomponent row. The diagonal cubic and container are the literal ones. -/
theorem source_hstar_cartan_normalizes_residual_of_psl25
    {M H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (U A B J : Subgroup G)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hJU : J ≤ normalizer (U : Set G))
    (hJ : (J.subgroupOf (normalizer (U : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hAJ : A ≤ normalizer (J : Set G))
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hA : IsPGroup 3 A) (hB : Nat.card B = 3)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 25)
    (eJ : (J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  let K := (pResidual 2 H).map H.subtype
  let N := normalizer (U : Set G)
  let := Chapter1.mem_L_isPerfect (source_hstar_residual_mem_local_of_a5 hH eK)
  have hQN : J.pCoreIn 2 ≤ N.pCoreIn 2 := by
    have hh := map_mono (f := N.subtype) (pCoreIn_le_of_subnormal 2 hJ.subnormal)
    rw [map_pCoreIn_of_injective 2 _ N.subtype N.subtype_injective,
      map_subgroupOf_eq_of_le hJU] at hh
    exact hh
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) :=
    hQN.trans ((pCoreIn_le_sylow N (T.subtype hTU)).trans_eq
      (map_subgroupOf_eq_of_le hTU))
  exact Theory.PSL2.TwentyFive.cartan_normalizes_perfect_subgroup K J A B
    hKJ hAJ hBA hBK
    (hQT.trans (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))) hA hB hF eJ

/-- The original fixed vector and Cartan irreducibility complete both
conclusions of9.3.1 in this actual container row. -/
theorem source_hstar_cartan_psl25_normalizes_and_centralizes
    {M H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (U A B J : Subgroup G)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hJU : J ≤ normalizer (U : Set G))
    (hJ : (J.subgroupOf (normalizer (U : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hAJ : A ≤ normalizer (J : Set G))
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hA : IsPGroup 3 A) (hB : Nat.card B = 3)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 25)
    (eJ : (J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)
    (hAU : A ≤ normalizer (U : Set G))
    (hirr : ∀ N : Subgroup G, N ≤ U → A ≤ normalizer (N : Set G) → N = ⊥ ∨ N = U)
    (z : G) (hz : z ≠ 1) (hzU : z ∈ U) (hzH : ∀ h ∈ H, h * z = z * h) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) := by
  have hn := source_hstar_cartan_normalizes_residual_of_psl25 hH eK U A B J
    hTU hJU hJ hKJ hAJ hBA hBK hA hB hF eJ
  exact ⟨hn,source_hstar_residual_centralizes_irreducible_line H U A hAU hirr hn z hz hzU hzH⟩

private theorem threeGroup_normalizes_cComponent
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (A J : Subgroup G)
    (hA : IsPGroup 3 A) (hJ : J.IsCComponent) : A ≤ normalizer (J : Set G) := by
  rcases Chapter1.Section02.component_normal_or_index_two_source hG hJ with hn | hi
  · let := hn
    exact le_normalizer_of_normal
  · let N := normalizer (J : Set G)
    let : N.Normal := normal_of_index_eq_two hi
    let q := QuotientGroup.mk' N
    have hp : IsPGroup 2 (G ⧸ N) := IsPGroup.of_card (n := 1) (by
      change N.index = 2 ^ 1
      simpa only [pow_one] using hi)
    have hb : A.map q = ⊥ := disjoint_self.mp
      ((hA.map q).disjoint_of_coprime (hp.to_subgroup _) (by decide))
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff A).mp hb

open Chapter3.Section02

/-- Literal four-group and noncentral cubic markings discharge irreducibility;
the SQTK component-orbit bound also supplies Cartan normalization of J. -/
theorem source_hstar_cartan_psl25_of_noncentral_cubic
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (U A B J : Subgroup G) (hU : Nat.card U = 4)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hJU : J ≤ normalizer (U : Set G))
    (hJ : (J.subgroupOf (normalizer (U : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hA : IsPGroup 3 A) (hB : Nat.card B = 3)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 25)
    (eJ : (J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)
    (hAU : A ≤ normalizer (U : Set G))
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdC : d ∉ centralizer (U : Set G))
    (z : G) (hz : z ≠ 1) (hzU : z ∈ U) (hzH : ∀ h ∈ H, h * z = z * h) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) := by
  let N := normalizer (U : Set G)
  have hUne : U ≠ ⊥ := by
    intro he
    simp only [he,Subgroup.card_bot] at hU
    omega
  have hUp : IsPGroup 2 U := IsPGroup.of_card (n := 2) hU
  have hN := D.simpleQTKE.twoLocal_sqtk (show IsTwoLocal N from ⟨U,hUne,hUp,rfl⟩)
  have hnJ := threeGroup_normalizes_cComponent hN (A.subgroupOf N) (J.subgroupOf N)
    hA.comap_subtype hJ
  rw [←subgroupOf_normalizer_eq hJU] at hnJ
  have hAJ : A ≤ normalizer (J : Set G) := fun a ha =>
    hnJ (show (⟨a,hAU ha⟩ : N) ∈ A.subgroupOf N from ha)
  apply source_hstar_cartan_psl25_normalizes_and_centralizes hH eK U A B J
    hTU hJU hJ hKJ hAJ hBA hBK hA hB hF eJ hAU ?_ z hz hzU hzH
  intro W hWU hAW
  exact Theory.GroupAction.CardFourCubic.invariant_ambient_subgroup U hU d
    (hAU hdA) hd3 hdC W hWU (hAW hdA)


/-- The PSL₂(25) source row feeds the original overgroup component proof.
The old residual's centralization and outside placement are both derived. -/
theorem source_hstar_psl25_tensor_pair_component_product
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (U A B J : Subgroup G) (hU : Nat.card U = 4)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hJU : J ≤ normalizer (U : Set G))
    (hJ : (J.subgroupOf (normalizer (U : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hA : IsPGroup 3 A) (hB : Nat.card B = 3)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 25)
    (eJ : (J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.PSL2MatrixGroup F)
    (hAU : A ≤ normalizer (U : Set G))
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdC : d ∉ centralizer (U : Set G))
    (z : G) (hz : z ≠ 1) (hzU : z ∈ U) (hzH : ∀ h ∈ H, h * z = z * h)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (hOldCore : H.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (E : Subgroup G) (hcore : pCore 2 E ≠ ⊥)
    (hgen : E = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hQ : L.pCoreIn 2 ≤ centralizer (componentOrbit U L : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (componentOrbit U L : Set G)) :
    (pResidual 2 E).IsCComponent ∧
      L.subgroupOf E ≤ pResidual 2 E ∧
      ((pResidual 2 H).map H.subtype).subgroupOf E ≤ pResidual 2 E ∧
      ∀ g : E, ∃ k ∈ pResidual 2 E,
        ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf E), k * r = g := by
  have hc := (source_hstar_cartan_psl25_of_noncentral_cubic D hH eK U A B J hU
    hTU hJU hJ hKJ hBA hBK hA hB hF eJ hAU d hdA hd3 hdC z hz hzU hzH).2
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  obtain ⟨_,hl,hout⟩ := source_a5_hstar_residual_at_stabilizer hTM hH eK hSyl hOldCore
  have hEout : ¬ E ≤ D.maximalLocal := by
    intro he
    exact hout ((hgen ▸ le_sup_of_le_left le_sup_right).trans he)
  exact source_a5_tensor_pair_component_product D eL hn E ((pResidual 2 H).map H.subtype)
    U hcore hgen hEout hl hQ hc hmove

end CFSG.Quasithin.Chapter10
