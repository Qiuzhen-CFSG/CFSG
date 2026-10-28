module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.BorelGeometry
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingOrbit

/-!
# Actual Borel actions on the paired source modules

A literal fifth-point marking identifies the elements of each original block
that lie in the point centralizer. Surjectivity of the marked alternating
image lifts every Borel actor to that intersection. Borel differences then
identify the embedded three-space with the commutator of the intersection
and the original block module.

This intrinsic description transports the three-space under any conjugation
preserving the point centralizer and carrying one marked block to another.
It retains the original action coordinates, including any twist in a block
exchange. The final consumer discharges the action hypotheses of the paired
Borel irreducibility theorem.

Source: Aschbacher--Smith, 14.6.9(k), printed p.1027, using the original
C.5.4 block markings and the binary permutation module of B.3.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open BinaryPermutation BinaryPermutation.AlternatingFiveFlag
open BinaryPermutation.AlternatingFiveBorel
variable {G : Type*} [Group G] {R K L Mc : Subgroup G}

/-- Every actual Borel actor lifts to the literal block intersection. -/
theorem AlternatingPairSetup.borel_lifts_of_point_marking
    (h : AlternatingPairSetup R K L)
    (hpoint : ∀ k : K, (k : G) ∈ Mc ↔ h.action (inclusion le_sup_left k) 4 = 4)
    (b : B) : ∃ k : K, (k : G) ∈ Mc ∧
      h.action (inclusion le_sup_left k) = b.val.val := by
  have hb : b.val.val ∈ (K.subgroupOf (K ⊔ ChapterB.baumann R)).map h.action :=
    h.block_image.symm ▸ b.val.property
  obtain ⟨g, hg, he⟩ := hb
  let k : K := ⟨g, hg⟩
  have hk : h.action (inclusion le_sup_left k) = b.val.val := he
  refine ⟨k, (hpoint k).mpr ?_, hk⟩
  rw [hk]
  exact b.property

private theorem borelMap_conjugation (h : AlternatingPairSetup R K L)
    (b : B) (g : K) (hg : h.action (inclusion le_sup_left g) = b.val.val) (v : V) :
    h.borelMap (act b v) = (g : G) * h.borelMap v * (g : G)⁻¹ := by
  have he := h.equivariant (inclusion le_sup_left g) (h.coordinates.symm v)
  rw [hg, h.coordinates.apply_symm_apply] at he
  exact he

private theorem borelMap_difference (h : AlternatingPairSetup R K L)
    (b : B) (g : K) (hg : h.action (inclusion le_sup_left g) = b.val.val) (v : V) :
    h.borelMap (Multiplicative.ofAdd (AlternatingFiveFlag.rho b.val.val v.toAdd - v.toAdd)) =
      ⁅(g : G), h.borelMap v⁆ := by
  rw [ofAdd_sub, div_eq_mul_inv]
  change h.borelMap (act b v * v⁻¹) = _
  rw [map_mul, map_inv, borelMap_conjugation h b g hg]
  rfl

/-- The marked three-space is the intrinsic moved module of the point centralizer. -/
theorem AlternatingPairSetup.borel_three_eq_commutator
    (h : AlternatingPairSetup R K L)
    (hpoint : ∀ k : K, (k : G) ∈ Mc ↔ h.action (inclusion le_sup_left k) 4 = 4) :
    three.map h.borelMap = ⁅K ⊓ Mc, sourceModule K⁆ := by
  apply le_antisymm
  · apply (map_le_iff_le_comap).mpr
    apply three_le_of_differences
    intro b x
    obtain ⟨k, hk, he⟩ := h.borel_lifts_of_point_marking hpoint b
    change h.borelMap (Multiplicative.ofAdd (rho b.val.val x - x)) ∈ ⁅K ⊓ Mc, sourceModule K⁆
    exact (borelMap_difference h b k he (Multiplicative.ofAdd x)).symm ▸
      commutator_mem_commutator ⟨k.property, hk⟩ (h.coordinates.symm _).property
  · apply commutator_le.mpr
    intro g hg u hu
    let k : K := ⟨g, hg.1⟩
    have heven : h.action (inclusion le_sup_left k) ∈ alternatingGroup (Fin 5) := by
      rw [← h.block_image]
      exact mem_map_of_mem h.action k.property
    let b : B := ⟨⟨h.action (inclusion le_sup_left k), heven⟩, (hpoint k).mp hg.2⟩
    let v : V := h.coordinates ⟨u, hu⟩
    have hv : h.borelMap v = u := congrArg Subtype.val (h.coordinates.symm_apply_apply ⟨u, hu⟩)
    have hd := mem_map_of_mem h.borelMap (difference_mem_three b v.toAdd)
    rw [borelMap_difference h b k rfl v, hv] at hd
    exact hd

/-- Conjugation transports the three-spaces without identifying their coordinates. -/
theorem AlternatingPairSetup.borel_three_map_conj
    {R' K' L' : Subgroup G}
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R' K' L')
    (hpoint : ∀ k : K, (k : G) ∈ Mc ↔ h.action (inclusion le_sup_left k) 4 = 4)
    (hpoint' : ∀ k : K', (k : G) ∈ Mc ↔ h'.action (inclusion le_sup_left k) 4 = 4)
    (t : G) (ht : t ∈ normalizer (Mc : Set G))
    (hKL : K.map (MulAut.conj t).toMonoidHom = K') :
    (three.map h.borelMap).map (MulAut.conj t).toMonoidHom = three.map h'.borelMap := by
  rw [h.borel_three_eq_commutator hpoint, h'.borel_three_eq_commutator hpoint',
    map_commutator, map_inf _ _ _ (MulAut.conj t).injective,
    sourceModule_map_equiv, hKL]
  have hm : Mc.map (MulAut.conj t).toMonoidHom = Mc := mem_normalizer_iff_map_conj_eq.mp ht
  rw [hm]

/-- Literal point markings and an actual block exchanger discharge the paired
Borel action inputs. The exchanger may act with arbitrary coordinate twists. -/
theorem AlternatingPairSetup.paired_borel_irreducible_of_point_markings
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (hpoint : ∀ k : K, (k : G) ∈ Mc ↔ h.action (inclusion le_sup_left k) 4 = 4)
    (hpoint' : ∀ k : L, (k : G) ∈ Mc ↔ h'.action (inclusion le_sup_left k) 4 = 4)
    (J : Subgroup G) (hKJ : K ⊓ Mc ≤ J) (hLJ : L ⊓ Mc ≤ J)
    (hexchange : ∃ t ∈ J, t ∈ normalizer (Mc : Set G) ∧
      K.map (MulAut.conj t).toMonoidHom = L) :
    Stellmacher.IsIrreducibleSection J
      (line.map h.borelMap ⊔ line.map h'.borelMap)
      (three.map h.borelMap ⊔ three.map h'.borelMap) := by
  apply h.paired_borel_irreducible_section h' J
  · intro b
    obtain ⟨k, hk, he⟩ := h.borel_lifts_of_point_marking hpoint b
    exact ⟨k, hKJ ⟨k.property, hk⟩, he⟩
  · intro b
    obtain ⟨k, hk, he⟩ := h'.borel_lifts_of_point_marking hpoint' b
    exact ⟨k, hLJ ⟨k.property, hk⟩, he⟩
  · obtain ⟨t, htJ, htMc, hKL⟩ := hexchange
    exact ⟨t, htJ, h.borel_three_map_conj h' hpoint hpoint' t htMc hKL⟩

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
