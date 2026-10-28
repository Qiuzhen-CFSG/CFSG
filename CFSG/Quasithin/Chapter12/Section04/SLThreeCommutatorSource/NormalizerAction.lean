module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Setup
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Contracts
public import Theory.Representation.SLThreeCentralExtension.Normalizer

/-!
# The full normalizer action on the original L₃ extension

For an element normalizing both L and V, conjugation preserves the original
fixed kernel and normalizes the marked L/O₂(L) action. The central-cover
normalizer theorem therefore identifies its action on V with an element of L.
The genuine known-simple uniqueness theorem identifies N_G(V) with N_G(L),
so this applies to every element of the full module normalizer.

Only the structural and marked-module implications of 12.2.2 remain explicit.
Their final discharge belongs to the original 12.4.2 assembly, using the 12.2
source producers. No fusion or fixed-space vanishing is used.

Source: Aschbacher–Smith, 12.2.10, printed p.798, and the L₃ setup preceding
12.4.5, printed pp.812–813; applied with the B.4.8 module geometry.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
open Section02 SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in
/-- On the original marked extension, every common normalizer of L and V
induces exactly the conjugation action of an element of L. -/
theorem same_action_of_common_normalizer (E : SLThreeExtension D)
    (n : G) (hnV : n ∈ normalizer (V : Set G))
    (hnL : n ∈ normalizer (L : Set G)) :
    ∃ l ∈ L, ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v := by
  let _ := D.elementary
  let a : MulAut V := V.normalizerMonoidHom ⟨n, hnV⟩
  let e : Additive V ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (a.toMonoidHom.toAdditive.toZModLinearMap 2) a.bijective
  have he (v : Additive V) : ((e v).toMul : G) = n * (v.toMul : G) * n⁻¹ := rfl
  have hker (v : Additive V) (hv : E.projection v = 0) : E.projection (e v) = 0 := by
    have hvf : v ∈ fixed E.action := by
      rw [← E.kernel]
      exact hv
    have hvc := (E.mem_fixed_iff v).mp hvf
    have hnc := normalizer_le_normalizer_centralizer L hnL
    apply (show fixed E.action ≤ E.projection.toLinearMap.ker from E.kernel.ge)
    apply (E.mem_fixed_iff (e v)).mpr
    rw [he]
    exact (hnc _).mp hvc
  have hnormal (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      ∃ h, ∀ v, e (E.action g v) = E.action h (e v) := by
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (E.quotientEquiv.symm g)
    have hlg : E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
      rw [hl, MulEquiv.apply_symm_apply]
    let k : L := ⟨n * (l : G) * n⁻¹, (hnL _).mp l.property⟩
    refine ⟨E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) k), fun v => ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [he, ← hlg, E.conjugation, E.conjugation, he]
    change n * ((l : G) * (v.toMul : G) * (l : G)⁻¹) * n⁻¹ =
      (n * (l : G) * n⁻¹) * (n * (v.toMul : G) * n⁻¹) * (n * (l : G) * n⁻¹)⁻¹
    group
  have hcover := isCover_of_indecomposable E.projection E.surjective E.kernel.le
    SLThreeCentralExtension.commutator_eq_top E.indecomposable
  obtain ⟨g, hg⟩ := SLThreeCentralExtension.normalizing_equiv_eq_action
    E.projection hcover e hker hnormal
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (E.quotientEquiv.symm g)
  have hlg : E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
    rw [hl, MulEquiv.apply_symm_apply]
  refine ⟨l, l.property, fun v hv => ?_⟩
  have hh := congrArg (fun x : Additive V => (x.toMul : G)) (hg (Additive.ofMul ⟨v, hv⟩))
  rw [he, ← hlg, E.conjugation] at hh
  exact hh

/-- Discharge the full-normalizer input from the two original 12.2 implications.
Known-simple uniqueness and the fixed line supply the normalizer equality. -/
theorem normalizerAction_of_structural_marked
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) : NormalizerAction.{u} := by
  intro G _ _ T L V h D hmodel hne n hn
  obtain ⟨E⟩ := marked G T L V h D hmodel hne
  obtain ⟨z, _, _, _, hnorm, _, _⟩ := fixed_involution_setup_of_card_two h D structural
    (E.fixed_card_eq_two hne)
  exact same_action_of_common_normalizer E n hn (by rwa [hnorm])

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource
