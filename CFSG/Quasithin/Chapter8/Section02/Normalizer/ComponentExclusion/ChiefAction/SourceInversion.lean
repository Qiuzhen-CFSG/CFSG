module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.SourceInversion.Quotient
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.SourceInversion.CoreIntersection
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.SourceInversion.Setup

/-!
# The source inverter and its bounded-section application

Source: Aschbacher–Smith, Lemma 8.2.7, printed p.718 (PDF p.735), with
compatible reselected 8.2.2–6 data.

For X=Ξ_p(K_U)=O²(H) and H=XT, the actual quotient H/O₂(H) has the
normal odd plane and an irreducible T-image. The rank-one V-image inverts
that plane; the quotient lift supplies exactly the inversion error required
by the component-invariant section constructor. The pair identity proves
P≤O₂(H). Minimal-parabolic maximality supplies IT=H, and the existing
Ξ APIs supply Sylow core containment and characteristic-two inheritance.

The result constructs and bounds the same section as ChiefAction, with no
inversion premise. The universal Chapter 1 inputs retain their source owners.
The stronger printed core equality still needs U≤X, isolated precisely in
CoreIntersection; it is unnecessary for this bound. Neither an affine
extension nor its degree estimate is constructed here.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
variable {G : Type*} [Group G] [Finite G]

/-- The source pair supplies both inversion and the constructor's generation,
core-containment and characteristic-two premises. The actual larger action
and its rank-ten bound are the ones constructed by ChiefAction. -/
theorem exists_bounded_component_section_of_source (p : ℕ) [Fact p.Prime] (hp : 3 < p) (K U V T Y H I M : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian p Y]
    (hXi : Chapter1.XiMember T (Chapter1.XiP p K))
    (hH : Chapter1.XiP p K ⊔ T = H)
    (S₂ : Sylow 2 H) (hS₂ : (S₂ : Subgroup H).map H.subtype = T)
    (hmin : ChapterB.IsMinimalParabolicOver S₂ ⊤)
    (hIH : I ≤ H)
    (hmax : M.subgroupOf H = ChapterB.minimalParabolicMax S₂ hmin)
    (hMI : I ⊓ M = I ⊓ normalizer (V : Set G))
    (g : G) (hg : g ∈ I)
    (hU : V ⊓ V.map (MulAut.conj g⁻¹).toMonoidHom = U)
    (h113 : ∀ M ∈ Chapter1.He G, ∀ N : Subgroup G, N ≠ ⊥ → N ≤ M →
      (N.subgroupOf M).IsSubnormal → N ∈ Chapter1.He G)
    (h114 : Chapter1.HOver G (T : Set G) ⊆ Chapter1.He G)
    (hTK : T ≤ normalizer (K : Set G))
    (hKU : K ≤ normalizer (U : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hYX : Y ≤ Chapter1.XiP p K)
    (S : Sylow p (Chapter1.XiP p K))
    (hS : (S : Subgroup (Chapter1.XiP p K)).map (Chapter1.XiP p K).subtype = Y)
    (hYcard : Nat.card Y = p ^ 2)
    (hq : Chapter1.XiOddQuotient p (Chapter1.XiQuotient (Chapter1.XiP p K)))
    (hres : Chapter1.XiP p K = (pResidual 2 H).map H.subtype)
    (hIC : I ≤ centralizer (U : Set G))
    (hVI : V ≤ I) (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hUB : U ≤ V ⊓ I.pCoreIn 2) (hk : (V ⊓ I.pCoreIn 2).relIndex V = 2)
    (hUcard : Nat.card U = 16) (hVcard : Nat.card V = 512 ∨ Nat.card V = 1024)
    (hP : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U) :
    let X := Chapter1.XiP p K
    let J := K ⊔ T
    let R := X.pCoreIn 2 ⊔ U
    ∃ hJR : J ≤ normalizer (R : Set G),
      ∃ D : Subgroup G, U ≤ D ∧ D < R ∧
        ∃ _hJD : J ≤ normalizer (D : Set G), ∃ hN : (D.subgroupOf R).Normal,
          let _ := hN
          ∃ ρ : J →* MulAut (R ⧸ D.subgroupOf R),
            (∀ j : J, ∀ r : R,
              ρ j (QuotientGroup.mk' (D.subgroupOf R) r) =
                QuotientGroup.mk' (D.subgroupOf R)
                  ⟨(j : G) * (r : G) * (j : G)⁻¹,
                    (mem_normalizer_iff.mp (hJR j.property) r).mp r.property⟩) ∧
            ∃ helem : IsElementaryAbelian 2 (R ⧸ D.subgroupOf R),
            let _ := helem
            Nontrivial (R ⧸ D.subgroupOf R) ∧
            (∀ A : Subgroup (R ⧸ D.subgroupOf R),
              (∀ j : J, ∀ w, w ∈ A → ρ j w ∈ A) → A = ⊥ ∨ A = ⊤) ∧
            commutatorAction ((Y.subgroupOf J).map ρ) (R ⧸ D.subgroupOf R) = ⊤ ∧
            ¬ Y.subgroupOf J ≤ ρ.ker ∧ (X.pCoreIn 2).subgroupOf J ≤ ρ.ker ∧
            Module.finrank (ZMod 2) (Additive (R ⧸ D.subgroupOf R)) ≤ 10 := by
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hT : Chapter1.IsSylowIn 2 T H := ⟨S₂, hS₂⟩
  have hQT := hXi.pCoreIn_le_of_isSylowIn (hT.restrict le_sup_right hH.le)
  have hUT : U ≤ T := hUB.trans (inf_le_left.trans hVT)
  have hUtwo : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 V).to_le (hUB.trans inf_le_left)
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hH]
    exact sup_le ((Chapter1.XiP_le p K).trans hKU) hTU
  have hodd : Odd (Nat.card (Chapter1.XiQuotient (Chapter1.XiP p K))) := by
    rcases hq with hq | hq
    · rw [hq.2]; exact ho.pow
    · rw [hq.2.1]; exact ho.pow
  have hcore := pair_core_le I H (Chapter1.XiP p K) U hIH hres
    (hUB.trans (inf_le_left.trans hVI)) hUtwo hHU hodd hP
  have hlocal : Chapter1.XiEmbedding.LocalInput p T (Chapter1.XiP p K) Y H := by
    have hl := Chapter1.XiEmbedding.localInput_of_mem_Xi hXi hT hH.le ho hq S
    rwa [hS] at hl
  obtain ⟨v, hinv⟩ := SourceInversion.exists_inverter_of_localInput hlocal hH hTV hIH hVI hcore hk
  have hUV : U < V := by
    apply lt_of_le_of_ne (hUB.trans inf_le_left)
    intro he
    have hc := congrArg (fun Z : Subgroup G => Nat.card Z) he
    rw [hUcard] at hc
    rcases hVcard with hv | hv <;> omega
  have hpair := SourceInversion.pair_sup_of_source_intersection I T H M U V S₂ hS₂
    hmin hIH hmax hMI g hg hU hUV
  exact exists_bounded_component_section p hp K U V T Y H I hTK hKU hTU hQT hUT
    (Chapter1.isSylowIn_iff.mp hT).1 hYX S hS hYcard hq.isPGroup (hXi.mem_He h113 h114)
    hres hpair hIC hVI hVT hTV hUB hk hUcard hVcard v hinv

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
