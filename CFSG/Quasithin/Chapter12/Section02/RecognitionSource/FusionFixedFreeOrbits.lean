module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionTransitive
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupTheory.ConjugationOrbitSize
public import Theory.Representation.OrbitSizeSeparation

/-!
# Orbit-size separation gives global TI on the original chosen module

Put N = N_G(L) ∩ N_G(V). Local TI and NoEscape put every nontrivial
point centralizer in N. Normalization preserves the L-orbit sizes;
separation therefore makes each N-orbit in V an L-orbit. Globally
conjugate points have equal centralizer orders, so orbit-stabilizer
makes their L-orbit sizes equal. Separation supplies an L-conjugator,
and the existing local-TI argument gives global TI.

No global fusion hypothesis is assumed. The remaining model calculations
must establish orbit separation for the actual action.
Source: Aschbacher--Smith 12.2.16, printed pp.799--800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

/-- Orbit sizes separate fusion on the unchanged original chosen module. -/
theorem globalTI_of_conjugacyOrbit_separation
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hsep : ∀ x y : G, x ∈ V → y ∈ V → x ≠ 1 → y ≠ 1 →
      (conjugacyOrbit L x).ncard = (conjugacyOrbit L y).ncard →
      ∃ l ∈ L, l * x * l⁻¹ = y) : IsTISubgroup V := by
  let N := normalizer (L : Set G) ⊓ normalizer (V : Set G)
  have hLN : L ≤ N := le_inf L.le_normalizer D.normalizes
  have hCN (x : G) (hx : x ∈ V) (hx1 : x ≠ 1) :
      centralizer ({x} : Set G) ≤ N :=
    le_inf (hnone x hx hx1)
      (point_centralizer_le_chosen_normalizer h D structural hnone hx hx1)
  have ho (x : G) (hx : x ∈ V) (hx1 : x ≠ 1) :
      conjugacyOrbit N x = conjugacyOrbit L x := by
    ext y
    constructor
    · rintro ⟨m,rfl⟩
      have hy : (m : G) * x * (m : G)⁻¹ ∈ V := (m.property.2 x).mp hx
      have hy1 : (m : G) * x * (m : G)⁻¹ ≠ 1 :=
        fun he => hx1 ((MulAut.conj (m : G)).map_eq_one_iff.mp he)
      obtain ⟨l,hl,he⟩ := hsep x _ hx hy hx1 hy1
        (conjugacyOrbit_normalizer L x m m.property.1).symm
      exact ⟨⟨l,hl⟩,he⟩
    · rintro ⟨l,rfl⟩
      exact ⟨⟨l,hLN l.property⟩,rfl⟩
  apply globalTI_of_fusion h D structural hnone
  intro x y hx hy hx1 hy1 hxy
  obtain ⟨g,rfl⟩ := hxy
  have hc : Nat.card (centralizer ({x} : Set G)) =
      Nat.card (centralizer ({g * x * g⁻¹} : Set G)) :=
    Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv
      (MulAut.conj g) x).toEquiv
  have hox := conjugacyOrbit_mul_centralizer N x (hCN x hx hx1)
  have hoy := conjugacyOrbit_mul_centralizer N (g*x*g⁻¹) (hCN _ hy hy1)
  rw [ho x hx hx1] at hox
  rw [ho _ hy hy1,← hc] at hoy
  have he := Nat.eq_of_mul_eq_mul_right
    (Nat.card_pos (α := centralizer ({x} : Set G))) (hox.trans hoy.symm)
  obtain ⟨l,hl,he⟩ := hsep x _ hx hy hx1 hy1 he
  exact ⟨l,L.le_normalizer hl,he⟩

/-- The model obligation is orbit separation for the literal chosen action. -/
theorem globalTI_of_chosen_orbit_separation
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (hsep : OrbitCardSeparates D.chosenAction) : IsTISubgroup V := by
  apply globalTI_of_conjugacyOrbit_separation h D structural hnone
  intro x y hx hy hx1 hy1 hcard
  let v := (D.spaceEquiv.symm ⟨x,hx⟩).toAdd
  let w := (D.spaceEquiv.symm ⟨y,hy⟩).toAdd
  let f : D.space → G := fun v => D.spaceEquiv (Multiplicative.ofAdd v)
  have hf : Function.Injective f := Subtype.val_injective.comp
    (D.spaceEquiv.injective.comp Multiplicative.ofAdd.injective)
  have hfv : f v = x := congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨x,hx⟩)
  have hfw : f w = y := congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨y,hy⟩)
  have hf0 : f 0 = 1 := congrArg Subtype.val D.spaceEquiv.map_one
  have he (l : L) (v : D.space) :
      f (D.chosenAction l v) = (l : G) * f v * (l : G)⁻¹ := by
    dsimp only [f]
    rw [D.spaceEquiv_apply,D.spaceEquiv_apply]
    rfl
  have himage (v : D.space) :
      f '' (Set.range fun l : L => D.chosenAction l v) = conjugacyOrbit L (f v) := by
    ext z
    constructor
    · rintro ⟨_,⟨l,rfl⟩,rfl⟩
      exact ⟨l,(he l v).symm⟩
    · rintro ⟨l,rfl⟩
      exact ⟨D.chosenAction l v,⟨l,rfl⟩,he l v⟩
  have hc : (Set.range fun l : L => D.chosenAction l v).ncard =
      (Set.range fun l : L => D.chosenAction l w).ncard := by
    rw [← Set.ncard_image_of_injective _ hf,← Set.ncard_image_of_injective _ hf,
      himage,himage,hfv,hfw]
    exact hcard
  have hv : v ≠ 0 := fun hz => hx1 (hfv.symm.trans ((congrArg f hz).trans hf0))
  have hw : w ≠ 0 := fun hz => hy1 (hfw.symm.trans ((congrArg f hz).trans hf0))
  obtain ⟨l,hl⟩ := hsep v w hv hw hc
  refine ⟨l,l.property,?_⟩
  have hh := congrArg f hl
  rwa [he,hfv,hfw] at hh

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
