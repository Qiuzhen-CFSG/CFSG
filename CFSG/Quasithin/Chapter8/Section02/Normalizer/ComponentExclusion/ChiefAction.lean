module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.Section
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.Bound

/-!
# The component-invariant chief action in Lemma 8.2.7

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 8.2.7, printed p.718 (PDF p.735).

The section is chosen invariant under K_U T from the outset. For the actual
radical X=Ξ_p(K_U)=O²(H), the canonical pair and the odd Sylow supplement
supply a nontrivial elementary irreducible quotient of O₂(X)U/U with full
odd support. Its action is literal conjugation and kills O₂(X).

Core proves O²(I)≤X and P≤O₂(H) from the source commutator identity, and
identifies V∩P with V∩O₂(H). Bound derives the rank-ten estimate from the
earlier table and inversion modulo O₂(H), using only V∩O₂(X)≤V∩P.
The stronger printed equality with V∩O₂(X) is not asserted here.

This is not the completed chief-action task or Lemma 8.2.7. The source
inversion premise and the actual faithful odd-plane extension in this SAME
action image remain to be proved. Final assembly of these inputs stays here;
ComponentExclusion retains the resulting quasisimplicity theorem. No degree
bound on the new section and no affine-extension conclusion is an input to
the section construction.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
variable {G : Type*} [Group G] [Finite G]

/-- Construct and bound one and the same K_U T-invariant section from the
source rows. Only the source inversion step remains explicit here; the
extension subgroup in its action image is a further source obligation. -/
theorem exists_bounded_component_section (p : ℕ) [Fact p.Prime] (hp : 3 < p) (K U V T Y H I : Subgroup G)
    [IsElementaryAbelian 2 V]
    (hTK : T ≤ normalizer (K : Set G))
    (hKU : K ≤ normalizer (U : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hQT : (Chapter1.XiP p K).pCoreIn 2 ≤ T) (hUT : U ≤ T) (hT : IsPGroup 2 T)
    (hYX : Y ≤ Chapter1.XiP p K)
    (S : Sylow p (Chapter1.XiP p K))
    (hS : (S : Subgroup (Chapter1.XiP p K)).map (Chapter1.XiP p K).subtype = Y)
    (hYcard : Nat.card Y = p ^ 2)
    (hquot : IsPGroup p ((Chapter1.XiP p K) ⧸ pCore 2 (Chapter1.XiP p K)))
    (hcentric : Chapter1.XiP p K ⊓ centralizer ((Chapter1.XiP p K).pCoreIn 2 : Set G) ≤
      (Chapter1.XiP p K).pCoreIn 2)
    (hres : Chapter1.XiP p K = (pResidual 2 H).map H.subtype)
    (hpair : I ⊔ T = H) (hIC : I ≤ centralizer (U : Set G))
    (hVI : V ≤ I) (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hUB : U ≤ V ⊓ I.pCoreIn 2) (hk : (V ⊓ I.pCoreIn 2).relIndex V = 2)
    (hUcard : Nat.card U = 16) (hVcard : Nat.card V = 512 ∨ Nat.card V = 1024)
    (v : V) (hinv : ∀ y ∈ Y, (v : G) * y * (v : G)⁻¹ * y ∈ H.pCoreIn 2) :
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
  let X := Chapter1.XiP p K
  let J := K ⊔ T
  let R := X.pCoreIn 2 ⊔ U
  obtain ⟨hJR, D, hUD, hDR, hJD, hN, ρ, hρ, helem, hnontriv, hirr, hfull, hactive, hker⟩ :=
    exists_component_section_of_sylow p hp K U T Y H I hTK hKU hTU hQT hUT hT hYX
      S hS hYcard hquot hcentric hres hpair hIC
  let _ := hN
  let _ := helem
  let _ := hnontriv
  have hJX : J ≤ normalizer (X : Set G) :=
    (sup_le K.le_normalizer hTK).trans (Chapter1.normalizer_le_normalizer_XiP p K)
  have hTH : T ≤ H := hpair ▸ le_sup_right
  have hIH : I ≤ H := hpair ▸ le_sup_left
  have hoddp : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hodd : Odd (Nat.card Y) := by rw [hYcard]; exact hoddp.pow
  let vJ : J := ⟨v, (show T ≤ J from le_sup_right) (hVT v.property)⟩
  have hbound := section_rank_from_source_rows X H I U V T J R D Y ρ hres hIH hVI hTH
    ((Chapter1.XiP_le p K).trans le_sup_left) hJX hQT hTV hVT hUT hUB hk hUcard hVcard
    le_rfl hUD hJR hρ hirr hYX hodd hactive hfull vJ v.property hinv
  exact ⟨hJR, D, hUD, hDR, hJD, hN, ρ, hρ, helem, hnontriv, hirr, hfull, hactive, hker, hbound⟩

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
