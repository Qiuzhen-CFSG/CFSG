module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration.Seeds
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import GorensteinWalter.PGL2CanonicalOuterInvolutionFusion
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# From representative configurations to all cyclic actors

Prime-field automorphism coverage puts every actor involution in PGL₂.
Inner involution fusion and diagonal outer involution fusion reduce it to
the two representative calculations. Conjugating an entire configuration
retains its PSL₂ conjugators because the PSL₂ image is normal in PGL₂.
An actual field equivalence then handles arbitrary finite field carriers.

The final theorem consumes both explicit seed premises; their construction
is the remaining part of the unconditional model-generation theorem.
Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453.
-/

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration
open Subgroup GorensteinWalter
open scoped MatrixGroups

private theorem conjugate_generation {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {t u : G} (htu : IsConj t u) {n : ℕ}
    (c : Fin n → N)
    (hc : N ≤ closure (Set.range fun i => (c i : G) * t * (c i : G)⁻¹)) :
    ∃ d : Fin n → N,
      N ≤ closure (Set.range fun i => (d i : G) * u * (d i : G)⁻¹) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp htu
  let d (i : Fin n) : N := ⟨g * c i * g⁻¹, (inferInstance : N.Normal).conj_mem _ (c i).property g⟩
  refine ⟨d, ?_⟩
  let H := closure (Set.range fun i => (d i : G) * (g * t * g⁻¹) * (d i : G)⁻¹)
  have hle : closure (Set.range fun i => (c i : G) * t * (c i : G)⁻¹) ≤
      H.comap (MulAut.conj g).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change g * ((c i : G) * t * (c i : G)⁻¹) * g⁻¹ ∈ H
    have he : g * ((c i : G) * t * (c i : G)⁻¹) * g⁻¹ =
        (d i : G) * (g * t * g⁻¹) * (d i : G)⁻¹ := by dsimp [d]; group
    rw [he]
    exact subset_closure ⟨i, rfl⟩
  intro x hx
  have hmem := hle (hc ((inferInstance : N.Normal).conj_mem x hx g⁻¹))
  change g * (g⁻¹ * x * (g⁻¹)⁻¹) * g⁻¹ ∈ H at hmem
  change x ∈ H
  simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
    mul_inv_cancel_right, mul_inv_cancel, mul_one] using hmem

private theorem map_generation {G H : Type*} [Group G] [Group H]
    (f : G →* H) (N : Subgroup G) {ι : Type*} (s : ι → G)
    (hs : N ≤ closure (Set.range s)) :
    N.map f ≤ closure (Set.range fun i => f (s i)) := by
  have hle : closure (Set.range s) ≤
      (closure (Set.range fun i => f (s i))).comap f := by
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact subset_closure ⟨i, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hle (hs hx)

private theorem range_conjugate_generation {S G : Type*} [Group S] [Group G]
    (f : S →* G) [f.range.Normal] {t u : G} (htu : IsConj t u)
    {n : ℕ} (c : Fin n → S)
    (hc : f.range ≤ closure (Set.range fun i => f (c i) * t * (f (c i))⁻¹)) :
    ∃ d : Fin n → S,
      f.range ≤ closure (Set.range fun i => f (d i) * u * (f (d i))⁻¹) := by
  classical
  obtain ⟨d, hd⟩ := conjugate_generation f.range htu
    (fun i => f.rangeRestrict (c i)) hc
  choose e he using fun i => (d i).property
  refine ⟨e, ?_⟩
  simpa only [he] using hd

private theorem prime_pgl_generation (hinner : InnerSeeds) (houter : OuterSeeds)
    (p : ℕ) [Fact p.Prime] (hp : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (t : PGL2 (ZMod p)) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ c : Fin 4 → PSL2 (ZMod p),
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range ≤
        closure (Set.range fun i => Matrix.ProjectiveSpecialLinearGroup.toPGL (c i) * t *
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (c i))⁻¹) := by
  let f : PSL2 (ZMod p) →* PGL2 (ZMod p) := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hf : Function.Injective f := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have ho : Odd p := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hlarge : 3 < p := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hK : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, ho, by omega, by simp⟩
  let : f.range.Normal := f.range.normal_of_index_eq_two
    (pgl2_psl2Range_index_eq_two (ZMod p) hK)
  by_cases htin : t ∈ f.range
  · obtain ⟨x, rfl⟩ := htin
    have hx : x ≠ 1 := by intro hx; apply ht; simp [hx]
    have hx2 : x ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using ht2)
    obtain ⟨r, hr, hr2, c, hc⟩ := hinner p hp
    have hconj := Theory.PSL2.involutions_isConj r x
      (orderOf_eq_prime hr2 hr) (orderOf_eq_prime hx2 hx)
    have hmap := map_generation f ⊤ (fun i => c i * r * (c i)⁻¹) hc.ge
    have hgen : f.range ≤ closure (Set.range fun i => f (c i) * f r * (f (c i))⁻¹) := by
      simpa only [← MonoidHom.range_eq_map, map_mul, map_inv] using hmap
    exact range_conjugate_generation f (f.map_isConj hconj) c hgen
  · obtain ⟨r, hr2, hrout, c, hc⟩ := houter p hp
    have hr : r ≠ 1 := by rintro rfl; exact hrout (one_mem _)
    have hconj := pgl2_outer_involutions_conjugate_of_odd_prime_power (ZMod p) hK
      (show IsInvolution r from ⟨hr, by simpa [pow_two] using hr2⟩)
      (show IsInvolution t from ⟨ht, by simpa [pow_two] using ht2⟩) hrout htin
    exact range_conjugate_generation f hconj c hc

private def InvolutionGeneration (S : Type*) [Group S] : Prop :=
  ∀ t : MulAut S, t ≠ 1 → t ^ 2 = 1 →
    ∃ c : Fin 4 → S, (MulAut.conj : S →* MulAut S).range ≤
      closure (Set.range fun i => MulAut.conj (c i) * t * (MulAut.conj (c i))⁻¹)

private theorem prime_involution_generation (hinner : InnerSeeds) (houter : OuterSeeds)
    (p : ℕ) [Fact p.Prime] (hp : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23) :
    InvolutionGeneration (PSL2 (ZMod p)) := by
  have ho : Odd p := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hlarge : 3 < p := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hK : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, ho, by omega, by simp⟩
  have hc : 3 < Nat.card (ZMod p) := by simpa using hlarge
  let f := pgl2InnerAutPSL2 (ZMod p) hK hc
  have hf : Function.Injective f := pgl2InnerAutPSL2_injective (ZMod p) hK hc
  intro t ht ht2
  obtain ⟨r, hr⟩ := Theory.PSL2.primeField_pgl_coverage ho hlarge t
  change f r = t at hr
  subst t
  have hr1 : r ≠ 1 := by intro hr1; apply ht; simp [hr1]
  have hr2 : r ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using ht2)
  obtain ⟨c, hgen⟩ := prime_pgl_generation hinner houter p hp r hr1 hr2
  have hmap := map_generation f _ _ hgen
  refine ⟨c, ?_⟩
  have himage : (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := ZMod p)).range.map f =
      (MulAut.conj : PSL2 (ZMod p) →* MulAut (PSL2 (ZMod p))).range := by
    rw [← MonoidHom.range_comp]
    apply congrArg MonoidHom.range
    apply MonoidHom.ext
    intro x
    exact pgl2InnerAutPSL2_toPGL (ZMod p) hK hc x
  rw [himage] at hmap
  simpa only [map_mul, map_inv, f, pgl2InnerAutPSL2_toPGL] using hmap

private theorem congr_conj {S T : Type*} [Group S] [Group T] (e : S ≃* T) (x : S) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr, MulAut.conj_apply]

private theorem involution_generation_equiv {S T : Type*} [Group S] [Group T]
    (e : S ≃* T) (h : InvolutionGeneration T) : InvolutionGeneration S := by
  intro t ht ht2
  let f := MulAut.congr e
  have ht' : f t ≠ 1 := fun he => ht (f.injective (he.trans (map_one f).symm))
  have ht2' : (f t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  obtain ⟨c, hc⟩ := h (f t) ht' ht2'
  have hmap := map_generation f.symm.toMonoidHom _ _ hc
  have himage : (MulAut.conj : T →* MulAut T).range.map f.symm.toMonoidHom =
      (MulAut.conj : S →* MulAut S).range := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e.symm x, congr_conj e.symm x |>.symm⟩
    · rintro _ ⟨x, rfl⟩
      refine mem_map.mpr ⟨MulAut.conj (e x), ⟨e x, rfl⟩, ?_⟩
      change MulAut.congr e.symm (MulAut.conj (e x)) = MulAut.conj x
      rw [congr_conj, e.symm_apply_apply]
  rw [himage] at hmap
  refine ⟨fun i => e.symm (c i), ?_⟩
  have htback : MulAut.congr e.symm (f t) = t := f.symm_apply_apply t
  simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, show f.symm = MulAut.congr e.symm from rfl,
    congr_conj, htback] using hmap

private theorem actor_generation_of_involutions {S : Type*} [Group S]
    (h : InvolutionGeneration S) : ActorGeneration S 2 4 := by
  intro A hA hcard
  let : IsElementaryAbelian 2 A := hA
  obtain ⟨t, ht, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
  have htne : (t : MulAut S) ≠ 1 := fun he => ht (Subtype.ext he)
  have ht2 : (t : MulAut S) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (t : MulAut S) t.property
  obtain ⟨c, hc⟩ := h t htne ht2
  refine ⟨c, hc.trans ?_⟩
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  apply mem_iSup_of_mem i
  exact mem_map.mpr ⟨t, t.property, rfl⟩

public theorem cyclicModelGeneration_of_seeds (hinner : InnerSeeds) (houter : OuterSeeds) :
    CyclicModelGeneration := by
  intro F _ _ q hq hF
  have hp : q.Prime := by rcases hq with rfl | rfl | rfl | rfl <;> decide
  let : Fact q.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod q := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hF, ZMod.card])
  exact actor_generation_of_involutions
    (involution_generation_equiv (psl2RingEquiv eF)
      (prime_involution_generation hinner houter q hq))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight.CyclicGeneration
