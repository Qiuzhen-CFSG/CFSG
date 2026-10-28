module

public import Theory.Representation.SL2FourCentralCover.Recognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover

/-!
# Six-dimensional coordinates and the literal Ru2 record

A natural SL₂(4) quotient of the original P/U with fixed kernel and full
commutator generation is indecomposable. A kernel of order four gives
binary dimension six. Transport the full supplied S₅ action and the
original section coordinates to Fin 6 → ZMod 2; invariant decompositions
restrict to the same alternating marking. This proves indecomposability
for S₅ without prescribing its action on the fixed kernel.

The final constructor uses exactly H=C_G(Z(T)), P=O₂(H), and U=⟨Vᴴ⟩.
It constructs the six-dimensional fields of RuTwo from the original section,
while retaining its natural action and actor quotient. It is a conditional
constructor, not a proof of 14.7.74 or 14.7.75. The P/U action, natural
projection, fixed kernel, commutator generation and kernel cardinality must
come from the preceding 14.7.73–74 argument. These obligations remain with
this source endgame; the final source assembly must discharge them.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.73–75 and Ru2 in J.1, printed pp.1076–1078 and 431.
-/

public section

open Representation Representation.OneCohomology Representation.SL2FourNatural
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
open ChapterJ

variable {G W : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- Construct the actual six-dimensional S₅ section from the original natural cover. -/
theorem exists_six_section
    (H P U : Subgroup G) (qH : H →* S5)
    (σ : Representation (ZMod 2) S5 W)
    (d : BinaryConjugationSection H P U (σ.comp qH))
    (a : L2FourAction)
    (p : Representation.IntertwiningMap (σ.comp (alternatingActor a)) naturalRepresentation)
    (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)))
    (hgen : Coinvariants.ker (σ.comp (alternatingActor a)) = ⊤)
    (hcard : Nat.card p.toLinearMap.ker = 4) :
    ∃ (τ : Representation (ZMod 2) S5 SixSpace) (e : W ≃ₗ[ZMod 2] SixSpace)
      (d₆ : BinaryConjugationSection H P U (τ.comp qH)),
      Indecomposable τ ∧
      (∀ g w, e (σ g w) = τ g (e w)) ∧
      (∀ x : P, (d₆.coordinates x).toAdd = e (d.coordinates x).toAdd) ∧
      ∃ e₀ : SL2FourCentralCover.binaryAction.Equiv (σ.comp (alternatingActor a)),
        ∀ w, p (e₀ w) = SL2FourCentralCover.projection w := by
  classical
  have hdimk : Module.finrank (ZMod 2) p.toLinearMap.ker = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := p.toLinearMap.ker)
    rw [Nat.card_zmod, hcard] at hc
    apply Nat.pow_right_injective (by decide : 1 < 2)
    exact hc.symm
  have hdim : Module.finrank (ZMod 2) W = 6 := by
    have h := p.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp, finrank_top, finrank_vector, hdimk] at h
    omega
  let e : W ≃ₗ[ZMod 2] SixSpace := LinearEquiv.ofFinrankEq _ _ (by
    simpa only [SixSpace, Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      mul_one] using hdim)
  let τ : Representation (ZMod 2) S5 SixSpace := e.conjRingEquiv.toMonoidHom.comp σ
  have he (g : S5) (w : W) : e (σ g w) = τ g (e w) := by
    change e (σ g w) = e (σ g (e.symm (e w)))
    rw [e.symm_apply_apply]
  have hind : Indecomposable τ := by
    intro A B hA hB hAB
    have hstable (X : Submodule (ZMod 2) SixSpace)
        (hX : ∀ g v, v ∈ X → τ g v ∈ X) :
        ∀ g v, v ∈ X.comap e.toLinearMap →
          σ (alternatingActor a g) v ∈ X.comap e.toLinearMap := by
      intro g v hv
      change e (σ (alternatingActor a g) v) ∈ X
      rw [he]
      exact hX _ _ hv
    have hc : IsCompl (A.comap e.toLinearMap) (B.comap e.toLinearMap) :=
      (Submodule.orderIsoMapComap e).symm.isCompl hAB
    have hh := SL2FourCentralCover.indecomposable_of_natural_cover p ⟨hp, hk, hgen⟩
      (A.comap e.toLinearMap) (B.comap e.toLinearMap) (hstable A hA) (hstable B hB) hc
    have hzero (X : Submodule (ZMod 2) SixSpace) (hX : X.comap e.toLinearMap = ⊥) :
        X = ⊥ := by
      apply bot_unique
      intro v hv
      have hmem : e.symm v ∈ X.comap e.toLinearMap := by
        change e (e.symm v) ∈ X
        simpa only [e.apply_symm_apply] using hv
      have hz : e.symm v = 0 := by
        rw [hX] at hmem
        exact hmem
      exact e.symm.injective (hz.trans e.symm.map_zero.symm)
    exact hh.elim (fun h => Or.inl (hzero A h)) (fun h => Or.inr (hzero B h))
  let c : P →* Multiplicative SixSpace :=
    e.toAddEquiv.toMultiplicative.toMonoidHom.comp d.coordinates
  have honto : Function.Surjective c := e.toAddEquiv.toMultiplicative.surjective.comp d.onto
  have hker : c.ker = U.subgroupOf P := by
    ext x
    change Multiplicative.ofAdd (e (d.coordinates x).toAdd) = 1 ↔ (x : G) ∈ U
    change e (d.coordinates x).toAdd = 0 ↔ (x : G) ∈ U
    rw [e.map_eq_zero_iff]
    exact d.coordinates_eq_one_iff x
  let d₆ : BinaryConjugationSection H P U (τ.comp qH) := {
    section_le := d.section_le
    kernel_le := d.kernel_le
    normalized := d.normalized
    coordinates := c
    onto := honto
    kernel_eq := hker
    equivariant := by
      intro h x
      change e (d.coordinates _).toAdd = τ (qH h) (e (d.coordinates x).toAdd)
      rw [d.equivariant h x]
      exact he (qH h) (d.coordinates x).toAdd }
  obtain ⟨e₀, h₀⟩ := SL2FourCentralCover.exists_equiv_of_six_dimensional_cover
    p ⟨hp, hk, hgen⟩ hdim
  exact ⟨τ, e, d₆, hind, he, (fun _ => rfl), e₀, h₀⟩

/-- Construct the literal Ru2 record once the source natural section and cover inputs are proved. -/
theorem exists_ruTwo_of_natural_and_cover
    (V : Subgroup G) (T : Sylow 2 G)
    (qH : centralizerOfSylowCenter T →* S5)
    (hq : Function.Surjective qH)
    (hqker : qH.ker = ((centralizerOfSylowCenter T).pCoreIn 2).subgroupOf
      (centralizerOfSylowCenter T))
    (a : L2FourAction)
    (dn : BinaryConjugationSection (centralizerOfSylowCenter T)
      (conjugateSpan (centralizerOfSylowCenter T) V) (sylowCenter T) (a.action.comp qH))
    (σ : Representation (ZMod 2) S5 W)
    (d : BinaryConjugationSection (centralizerOfSylowCenter T)
      ((centralizerOfSylowCenter T).pCoreIn 2)
      (conjugateSpan (centralizerOfSylowCenter T) V) (σ.comp qH))
    (p : Representation.IntertwiningMap (σ.comp (alternatingActor a)) naturalRepresentation)
    (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)))
    (hgen : Coinvariants.ker (σ.comp (alternatingActor a)) = ⊤)
    (hcard : Nat.card p.toLinearMap.ker = 4) :
    Nonempty (RuTwo V T) := by
  obtain ⟨τ, _, d₆, hind, _, _⟩ := exists_six_section _ _ _ qH σ d a p hp hk hgen hcard
  exact ⟨{
    quotientMap := qH
    quotient_surjective := hq
    quotient_kernel := hqker
    naturalAction := a
    natural := dn
    sixAction := τ
    indecomposable := hind
    six := d₆ }⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
