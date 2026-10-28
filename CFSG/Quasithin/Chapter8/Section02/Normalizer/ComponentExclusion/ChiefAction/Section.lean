module

public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Theory.GroupAction.PGroupNoncentralQuotientModulo
public import Theory.GroupTheory.TwoPerfectOddSupplement
public import CFSG.Quasithin.Chapter1.Section03.Radical.Defs
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.Action


/-!
# A section invariant under the actual containing component

Source: Aschbacher–Smith, Lemma 8.2.7, printed p.718 (PDF p.735).

Set X=Ξ_p(K_U), J=K_U T and R=O₂(X)U. Characteristicity of Ξ_p(K_U)
shows that J normalizes R. The odd Sylow supplement acts fully on O₂(X)
because X is two-perfect. The canonical pair I centralizes U, and H=IT
makes O²(H)=X centralize U as well. A nontrivial two-core therefore does
not lie in U. The invariant-denominator construction gives a nontrivial
elementary J-irreducible section of R/U with full Y-support and literal
conjugation action. This same action kills O₂(X).

The last theorem derives the supplement and nontrivial two-core from the
literal Sylow plane, p-group quotient and characteristic-two centralizer
condition. These are earlier-source data. No chief-section dimension is
assumed. Identifying an affine extension in this action image, and deriving
the source inverting element, remain separate obligations.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
variable {G : Type*} [Group G] [Finite G]

/-- Construct the section using K_U T from the start. The odd supplement, nontrivial two-core and centralization of U are
explicit earlier-source premises. Properness and full support are proved. -/
theorem exists_component_section (p : ℕ) (K U T Y : Subgroup G)
    (hTK : T ≤ normalizer (K : Set G))
    (hKU : K ≤ normalizer (U : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hQT : (Chapter1.XiP p K).pCoreIn 2 ≤ T) (hUT : U ≤ T) (hT : IsPGroup 2 T)
    (hYX : Y ≤ Chapter1.XiP p K)
    (hodd : Odd (Nat.card Y))
    (hgen : (Chapter1.XiP p K).pCoreIn 2 ⊔ Y = Chapter1.XiP p K)
    (hQne : (Chapter1.XiP p K).pCoreIn 2 ≠ ⊥)
    (hUY : U ≤ centralizer (Y : Set G)) :
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
            IsElementaryAbelian 2 (R ⧸ D.subgroupOf R) ∧
            Nontrivial (R ⧸ D.subgroupOf R) ∧
            (∀ A : Subgroup (R ⧸ D.subgroupOf R),
              (∀ j : J, ∀ w, w ∈ A → ρ j w ∈ A) → A = ⊥ ∨ A = ⊤) ∧
            commutatorAction ((Y.subgroupOf J).map ρ) (R ⧸ D.subgroupOf R) = ⊤ ∧
            ¬ Y.subgroupOf J ≤ ρ.ker ∧ (X.pCoreIn 2).subgroupOf J ≤ ρ.ker := by
  dsimp only
  let X := Chapter1.XiP p K
  let J := K ⊔ T
  let R := X.pCoreIn 2 ⊔ U
  have hJX : J ≤ normalizer (X : Set G) :=
    (sup_le K.le_normalizer hTK).trans (Chapter1.normalizer_le_normalizer_XiP p K)
  have hJU : J ≤ normalizer (U : Set G) := sup_le hKU hTU
  have hJR : J ≤ normalizer (R : Set G) :=
    (le_inf (hJX.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))) hJU).trans
      (normalizer_inf_normalizer_le_normalizer_sup (X.pCoreIn 2) U)
  have hRJ : R ≤ J := sup_le
    ((pCoreIn_le 2 X).trans ((Chapter1.XiP_le p K).trans le_sup_left))
    (hUT.trans le_sup_right)
  have hYJ : Y ≤ J := hYX.trans ((Chapter1.XiP_le p K).trans le_sup_left)
  have hQfull : ⁅X.pCoreIn 2, Y⁆ = X.pCoreIn 2 :=
    embedded_commutator_two_core_eq_of_odd_supplement X Y hYX
      (Chapter1.XiP_isPPerfect p K) hodd hgen
  have hproper : ¬ X.pCoreIn 2 ≤ U := by
    intro hQU
    apply hQne
    rw [← hQfull]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hQU.trans hUY)
  have hUR : U < R := lt_of_le_of_ne le_sup_right (by
    intro he
    exact hproper (he.symm ▸ (show X.pCoreIn 2 ≤ R from le_sup_left)))
  have hfull : ⁅R, Y⁆ ⊔ U = R := by
    apply le_antisymm
      (sup_le (le_normalizer_iff_commutator_le_left.mp (hYJ.trans hJR)) le_sup_right)
    exact sup_le (hQfull.symm.le.trans (commutator_mono le_sup_left le_rfl) |>.trans le_sup_left)
      le_sup_right
  obtain ⟨D, hUD, hDR, hJD, hN, ρ, hρ, helem, hnontriv, hirr, hsupport, hactive⟩ :=
    exists_noncentral_irreducible_quotient_modulo J R U Y hRJ hJR hJU hUR
      (hT.to_le (sup_le hQT hUT)) hYJ hfull
  let _ := hN
  let _ := helem
  let _ := hnontriv
  exact ⟨hJR, D, hUD, hDR, hJD, hN, ρ, hρ, helem, hnontriv, hirr, hsupport,
    hactive, core_killed J X ρ hJX hirr⟩

/-- The canonical pair centralizes U, and H=IT, so the two-residual X
centralizes U. This discharges the centralization input of the larger-actor
section construction directly from the source pair. -/
theorem exists_component_section_of_pair (p : ℕ) (K U T Y H I : Subgroup G)
    (hTK : T ≤ normalizer (K : Set G))
    (hKU : K ≤ normalizer (U : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hQT : (Chapter1.XiP p K).pCoreIn 2 ≤ T) (hUT : U ≤ T) (hT : IsPGroup 2 T)
    (hYX : Y ≤ Chapter1.XiP p K)
    (hodd : Odd (Nat.card Y))
    (hgen : (Chapter1.XiP p K).pCoreIn 2 ⊔ Y = Chapter1.XiP p K)
    (hQne : (Chapter1.XiP p K).pCoreIn 2 ≠ ⊥)
    (hres : Chapter1.XiP p K = (pResidual 2 H).map H.subtype)
    (hpair : I ⊔ T = H) (hIC : I ≤ centralizer (U : Set G)) :
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
            IsElementaryAbelian 2 (R ⧸ D.subgroupOf R) ∧
            Nontrivial (R ⧸ D.subgroupOf R) ∧
            (∀ A : Subgroup (R ⧸ D.subgroupOf R),
              (∀ j : J, ∀ w, w ∈ A → ρ j w ∈ A) → A = ⊥ ∨ A = ⊤) ∧
            commutatorAction ((Y.subgroupOf J).map ρ) (R ⧸ D.subgroupOf R) = ⊤ ∧
            ¬ Y.subgroupOf J ≤ ρ.ker ∧ (X.pCoreIn 2).subgroupOf J ≤ ρ.ker := by
  have hXC : Chapter1.XiP p K ≤ centralizer (U : Set G) := by
    rw [hres]
    exact Normalizer.residual_centralizes H I T U hpair hT hIC hTU
  exact exists_component_section p K U T Y hTK hKU hTU hQT hUT hT hYX hodd hgen hQne
    (le_centralizer_iff.mp (hYX.trans hXC))

/-- For the literal Sylow p-plane, the p-group quotient gives the supplement,
and characteristic two gives the nontrivial two-core. No section bound or
noncentral chief factor is supplied as a premise. -/
theorem exists_component_section_of_sylow (p : ℕ) [Fact p.Prime] (hp : 3 < p) (K U T Y H I : Subgroup G)
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
    (hpair : I ⊔ T = H) (hIC : I ≤ centralizer (U : Set G)) :
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
            IsElementaryAbelian 2 (R ⧸ D.subgroupOf R) ∧
            Nontrivial (R ⧸ D.subgroupOf R) ∧
            (∀ A : Subgroup (R ⧸ D.subgroupOf R),
              (∀ j : J, ∀ w, w ∈ A → ρ j w ∈ A) → A = ⊥ ∨ A = ⊤) ∧
            commutatorAction ((Y.subgroupOf J).map ρ) (R ⧸ D.subgroupOf R) = ⊤ ∧
            ¬ Y.subgroupOf J ≤ ρ.ker ∧ (X.pCoreIn 2).subgroupOf J ≤ ρ.ker := by
  let X := Chapter1.XiP p K
  have hoddp : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hodd : Odd (Nat.card Y) := by rw [hYcard]; exact hoddp.pow
  have hgen : X.pCoreIn 2 ⊔ Y = X := by
    have h := congrArg (map X.subtype) (S.sup_eq_top_of_quotient_isPGroup (pCore 2 X) hquot)
    rw [Subgroup.map_sup, hS, ← MonoidHom.range_eq_map, range_subtype] at h
    exact (sup_comm _ _).trans h
  have hQne : X.pCoreIn 2 ≠ ⊥ := by
    intro hQ
    have hXbot : X = ⊥ := by
      apply bot_unique
      intro x hx
      have hc : x ∈ centralizer (X.pCoreIn 2 : Set G) := by
        intro q hq
        have hq1 : q = 1 := mem_bot.mp (hQ ▸ hq)
        simp only [hq1, one_mul, mul_one]
      have hm := hcentric ⟨hx, hc⟩
      exact hQ ▸ hm
    have hYbot : Y = ⊥ := bot_unique (hXbot ▸ hYX)
    have hYone : Nat.card Y = 1 := (eq_bot_iff_card Y).mp hYbot
    have hp2 : 1 < p ^ 2 := one_lt_pow₀ (by omega : 1 < p) (by decide)
    omega
  exact exists_component_section_of_pair p K U T Y H I hTK hKU hTU hQT hUT hT hYX
    hodd hgen hQne hres hpair hIC

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
