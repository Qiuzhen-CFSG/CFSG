module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.Factors
public import Theory.SpecificGroups.Suzuki.RootOmega

/-!
# Fixed-point counting for a covered Suzuki pair

The literal factor permutation makes the stabilizer of K have index two
in any subgroup containing a swapping element. On elements of the component
orbit fixed by that element, projection to the first quotient coordinate
is injective modulo the full central kernel. Thus the fixed subgroup's
quotient image has order at most q, while the full omega image has order q².
Kernel–image counting gives q |C_Ω(u)| ≤ |Ω|, without assuming that the
central extension splits or that its center is fixed pointwise.

These are the counting inputs to ThompsonComparison, which rules out a
swapping element in a largest elementary abelian subgroup.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 / PDF p.944.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
variable {G : Type*} [Group G] {T K : Subgroup G} {v : G}
namespace PairFactors
variable {d : Marking T K v} (c : PairFactors d)

private theorem swaps_of_not_normalizes (u : Tv T v) (hu : (u : G) ∉ normalizer (K : Set G)) :
    K.map (MulAut.conj (u : G)).toMonoidHom =
        K.map (MulAut.conj (c.moving : G)).toMonoidHom ∧
      (K.map (MulAut.conj (c.moving : G)).toMonoidHom).map
        (MulAut.conj (u : G)).toMonoidHom = K := by
  exact (c.permutation u).resolve_left (fun h => hu
    (mem_normalizer_iff_map_conj_eq.mpr h.1))

include c in
/-- The actual factor stabilizer has index two whenever the subgroup moves K. -/
theorem stabilizer_relIndex (A : Subgroup G) (hAT : A ≤ Tv T v)
    (u : A) (hu : (u : G) ∉ normalizer (K : Set G)) :
    (normalizer (K : Set G)).relIndex A = 2 := by
  apply relIndex_eq_two_iff_exists_notMem_and.mpr
  refine ⟨u, u.property, hu, ?_⟩
  intro b hb
  by_cases hbN : b ∈ normalizer (K : Set G)
  · exact Or.inr hbN
  · left
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hu' := c.swaps_of_not_normalizes ⟨u, hAT u.property⟩ hu
    have hb' := c.swaps_of_not_normalizes ⟨b, hAT hb⟩ hbN
    calc
      K.map (MulAut.conj (b * u)).toMonoidHom =
          (K.map (MulAut.conj (u : G)).toMonoidHom).map
            (MulAut.conj b).toMonoidHom := by
        rw [map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      _ = K := by rw [hu'.1, hb'.2]

include c in
/-- On elements fixed by a swapping element, the first quotient coordinate
has trivial kernel modulo the full central kernel. -/
private theorem fixed_quotient_fst_eq_one (hKG : K ≤ Gv v)
    (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    (u : Tv T v) (hu : (u : G) ∉ normalizer (K : Set G))
    (x : orbit T K v) (hx : Commute (u : G) (x : G))
    (hfst : (d.quotientMap x).1 = 1) : d.quotientMap x = 1 := by
  let a := orbitAction T K v u
  obtain ⟨k, l, hkl⟩ := c.factorization hKG hK x
  have hk : d.quotientMap (firstEmbedding T K v k) = 1 := by
    have h := hfst
    rw [← hkl, map_mul, c.first_eq, c.second_eq] at h
    apply Prod.ext
    · simpa only [c.first_eq, Prod.fst_mul, Prod.fst_one, mul_one] using h
    · simp only [c.first_eq, Prod.snd_one]
  have hkZ : firstEmbedding T K v k ∈ center (orbit T K v) := by
    rw [← d.quotientMap_ker]
    exact hk
  have hak : d.quotientMap (a (firstEmbedding T K v k)) = 1 := by
    change a (firstEmbedding T K v k) ∈ d.quotientMap.ker
    rw [d.quotientMap_ker]
    exact (centerCongr a ⟨firstEmbedding T K v k, hkZ⟩).property
  have halK : (a (secondEmbedding T K v c.moving l) : G) ∈ K := by
    have hs := (c.swaps_of_not_normalizes u hu).2
    exact hs.le (mem_map_of_mem _ (mem_map_of_mem _ l.property))
  let z : K := ⟨a (secondEmbedding T K v c.moving l), halK⟩
  have hal : a (secondEmbedding T K v c.moving l) = firstEmbedding T K v z :=
    Subtype.ext rfl
  have hax : a x = x := by
    apply Subtype.ext
    change (u : G) * (x : G) * (u : G)⁻¹ = x
    rw [hx.eq, mul_inv_cancel_right]
  apply Prod.ext hfst
  calc
    (d.quotientMap x).2 = (d.quotientMap (a x)).2 := by rw [hax]
    _ = 1 := by rw [← hkl, map_mul, map_mul, hak, hal, c.first_eq, one_mul]

variable [Finite G]

private theorem card_kernel_mul_image {H Q : Type*} [Group H] [Group Q]
    (f : H →* Q) (B : Subgroup H) :
    Nat.card (f.ker ⊓ B : Subgroup H) * Nat.card (B.map f) = Nat.card B := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup H) (f.ker ⊓ B) B bot_le inf_le_right
  simpa only [relIndex_bot_left, inf_relIndex_right, relIndex_ker] using h

include c in
/-- A swapping element loses at least one full root omega in its fixed subgroup,
even when the central kernel is nontrivial. -/
theorem omega_fixed_card_bound (hKG : K ≤ Gv v)
    (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    (himage : ((omega T K v).subgroupOf (orbit T K v)).map d.quotientMap =
      (omegaOneAmbient (SuzukiRootSubgroup d.parameter)).prod
        (omegaOneAmbient (SuzukiRootSubgroup d.parameter)))
    (u : Tv T v) (hu : (u : G) ∉ normalizer (K : Set G)) :
    2 ^ (2 * d.parameter + 1) *
        Nat.card (omega T K v ⊓ centralizer ({(u : G)} : Set G) : Subgroup G) ≤
      Nat.card (omega T K v) := by
  let E := omegaOneAmbient (SuzukiRootSubgroup d.parameter)
  let W := (omega T K v).subgroupOf (orbit T K v)
  let C := omega T K v ⊓ centralizer ({(u : G)} : Set G)
  let D := C.subgroupOf (orbit T K v)
  have hWO : omega T K v ≤ orbit T K v := (omegaOneAmbient_le _).trans inf_le_right
  have hDC : Nat.card D = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hWO)).toEquiv
  have hWW : Nat.card W = Nat.card (omega T K v) :=
    Nat.card_congr (subgroupOfEquivOfLe hWO).toEquiv
  have hDW : D ≤ W := fun _ hx => hx.1
  have hmap : D.map d.quotientMap ≤ E.prod E :=
    (map_mono hDW).trans himage.le
  let f : D.map d.quotientMap →* E :=
    (((MonoidHom.fst _ _).comp (D.map d.quotientMap).subtype).codRestrict E
      (fun x => (hmap x.property).1))
  have hfi : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro y hy
    apply Subtype.ext
    obtain ⟨x, hx, hxy⟩ := y.property
    rw [← hxy]
    apply c.fixed_quotient_fst_eq_one hKG hK u hu x
    · exact (mem_centralizer_singleton_iff.mp hx.2).symm
    · have h := congrArg Subtype.val hy
      change (y : SuzukiMatrixGroup d.parameter × SuzukiMatrixGroup d.parameter).1 = 1 at h
      rwa [hxy]
  have hsmall : Nat.card (D.map d.quotientMap) ≤ Nat.card E :=
    Nat.card_le_card_of_injective f hfi
  have hker : Nat.card (d.quotientMap.ker ⊓ D : Subgroup (orbit T K v)) ≤
      Nat.card (d.quotientMap.ker ⊓ W : Subgroup (orbit T K v)) :=
    card_le_of_le (inf_le_inf_left _ hDW)
  have hD := card_kernel_mul_image d.quotientMap D
  have hW := card_kernel_mul_image d.quotientMap W
  have hprod : Nat.card (W.map d.quotientMap) = Nat.card E * Nat.card E := by
    rw [himage, Nat.card_congr (prodEquiv E E).toEquiv, Nat.card_prod]
  rw [hprod] at hW
  have hbound : Nat.card E * Nat.card D ≤ Nat.card W := calc
    Nat.card E * Nat.card D = Nat.card E *
        (Nat.card (d.quotientMap.ker ⊓ D : Subgroup (orbit T K v)) *
          Nat.card (D.map d.quotientMap)) := by rw [hD]
    _ ≤ Nat.card E *
        (Nat.card (d.quotientMap.ker ⊓ W : Subgroup (orbit T K v)) * Nat.card E) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hker hsmall)
    _ = Nat.card W := by rw [← hW]; ac_rfl
  rw [hDC, hWW, suzukiRootSubgroup_omega_card d.parameter d.positive] at hbound
  exact hbound


end PairFactors
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
