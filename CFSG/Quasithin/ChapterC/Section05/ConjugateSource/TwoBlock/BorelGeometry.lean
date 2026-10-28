module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPair
public import Theory.Representation.BinaryAlternatingFiveFlag.PairedBorelTransport
public import Mathlib.GroupTheory.NoncommCoprod
public import Stellmacher.SectionsOneToFourDefs

/-!
# The paired Borel section on the original alternating block markings

The two existing C.5 block markings define literal embedded three-spaces
and their fixed lines. Cross-block commutation and the trivial fixed kernel
make their coordinate product injective. Lifts of the actual A₄ point
stabilizers through each marked block action then give independent Borel
actors; a source element exchanging the two three-spaces supplies the
remaining action. Their joins have orders 64 and 4, and the marked
irreducibility theorem forces the six-space into any normalized subgroup
meeting it outside the fixed plane.

The original point-Borel lifts and the exchanging element remain explicit
inputs, produced by the paired point-centralizer source geometry. The source
14.6.9(k) assembly supplies the normalized subgroup and nonzero intersection.
No abstract identification of the ambient paired extension is assumed.

Source: Aschbacher--Smith, 14.6.9(k), printed p.1027; the markings are those
of C.5.4 and the binary five-point module of B.3.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open BinaryPermutation BinaryPermutation.AlternatingFiveFlag
open BinaryPermutation.AlternatingFiveBorel
variable {G : Type*} [Group G] {R K L : Subgroup G}

def AlternatingPairSetup.borelMap (h : AlternatingPairSetup R K L) : V →* G :=
  (sourceModule K).subtype.comp h.coordinates.symm.toMonoidHom

theorem AlternatingPairSetup.borel_pair_commute
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (u v : V) : Commute (h.borelMap u) (h'.borelMap v) :=
  (h.commute ((map_subtype_le _) (h'.coordinates.symm v).property)
    (h.borelMap u) ((map_subtype_le _) (h.coordinates.symm u).property))

def AlternatingPairSetup.borelPairMap
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K) : V × V →* G :=
  h.borelMap.noncommCoprod h'.borelMap (h.borel_pair_commute h')

theorem AlternatingPairSetup.borelPairMap_apply
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K) (x : V × V) :
    h.borelPairMap h' x = h.borelMap x.1 * h'.borelMap x.2 := rfl

theorem AlternatingPairSetup.borelPairMap_injective
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K) :
    Function.Injective (h.borelPairMap h') := by
  have hd : Disjoint (sourceModule K) (sourceModule L) :=
    alternatingModule_disjoint_of_commuting K (sourceModule L) h.block
      ((map_subtype_le _).trans h.commute)
  intro x y hxy
  have he : (h.coordinates.symm x.1, h'.coordinates.symm x.2) =
      (h.coordinates.symm y.1, h'.coordinates.symm y.2) :=
    mul_injective_of_disjoint hd hxy
  exact Prod.ext (h.coordinates.symm.injective (congrArg Prod.fst he))
    (h'.coordinates.symm.injective (congrArg Prod.snd he))

theorem AlternatingPairSetup.borelPairMap_prod
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (A B : Subgroup V) :
    (A.prod B).map (h.borelPairMap h') = A.map h.borelMap ⊔ B.map h'.borelMap := by
  apply le_antisymm
  · rintro y ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact mul_mem_sup (mem_map_of_mem h.borelMap ha) (mem_map_of_mem h'.borelMap hb)
  · apply sup_le
    · rintro y ⟨a, ha, rfl⟩
      refine ⟨(a, 1), ⟨ha, B.one_mem⟩, ?_⟩
      simp only [h.borelPairMap_apply, map_one, mul_one]
    · rintro y ⟨b, hb, rfl⟩
      refine ⟨(1, b), ⟨A.one_mem, hb⟩, ?_⟩
      simp only [h.borelPairMap_apply, map_one, one_mul]

private theorem borelMap_conjugation (h : AlternatingPairSetup R K L)
    (b : B) (g : K) (hg : h.action (inclusion le_sup_left g) = b.val.val) (v : V) :
    h.borelMap (act b v) = (g : G) * h.borelMap v * (g : G)⁻¹ := by
  have he := h.equivariant (inclusion le_sup_left g) (h.coordinates.symm v)
  rw [hg, h.coordinates.apply_symm_apply] at he
  exact he

def AlternatingPairSetup.pairedBorelCoordinates
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (J : Subgroup G)
    (hfirst : ∀ b : B, ∃ g : K, (g : G) ∈ J ∧
      h.action (inclusion le_sup_left g) = b.val.val)
    (hsecond : ∀ b : B, ∃ g : L, (g : G) ∈ J ∧
      h'.action (inclusion le_sup_left g) = b.val.val)
    (hexchange : ∃ t ∈ J,
      (three.map h.borelMap).map (MulAut.conj t).toMonoidHom = three.map h'.borelMap) :
    PairedBorelCoordinates J where
  embedding := h.borelPairMap h'
  injective := h.borelPairMap_injective h'
  first_actor := by
    intro b
    obtain ⟨g, hgJ, hg⟩ := hfirst b
    refine ⟨g, hgJ, ?_⟩
    intro x
    have he := borelMap_conjugation h b g hg x.1
    have hc : (g : G) * h'.borelMap x.2 * (g : G)⁻¹ = h'.borelMap x.2 := by
      have hh := h'.commute g.property (h'.borelMap x.2)
        ((map_subtype_le _) (h'.coordinates.symm x.2).property)
      exact mul_inv_eq_iff_eq_mul.mpr hh.symm
    rw [h.borelPairMap_apply, h.borelPairMap_apply, he]
    change _ = MulAut.conj (g : G) (h.borelMap x.1 * h'.borelMap x.2)
    rw [map_mul]
    change _ = ((g : G) * h.borelMap x.1 * (g : G)⁻¹) *
      ((g : G) * h'.borelMap x.2 * (g : G)⁻¹)
    rw [hc]
  second_actor := by
    intro b
    obtain ⟨g, hgJ, hg⟩ := hsecond b
    refine ⟨g, hgJ, ?_⟩
    intro x
    have he := borelMap_conjugation h' b g hg x.2
    have hc : (g : G) * h.borelMap x.1 * (g : G)⁻¹ = h.borelMap x.1 := by
      have hh := h.commute g.property (h.borelMap x.1)
        ((map_subtype_le _) (h.coordinates.symm x.1).property)
      exact mul_inv_eq_iff_eq_mul.mpr hh.symm
    rw [h.borelPairMap_apply, h.borelPairMap_apply, he]
    change _ = MulAut.conj (g : G) (h.borelMap x.1 * h'.borelMap x.2)
    rw [map_mul]
    change _ = ((g : G) * h.borelMap x.1 * (g : G)⁻¹) *
      ((g : G) * h'.borelMap x.2 * (g : G)⁻¹)
    rw [hc]
  exchange := by
    obtain ⟨t, ht, he⟩ := hexchange
    refine ⟨t, ht, ?_⟩
    simpa only [h.borelPairMap_prod, Subgroup.map_bot, sup_bot_eq, bot_sup_eq] using he

theorem AlternatingPairSetup.paired_borel_geometry
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (J : Subgroup G)
    (hfirst : ∀ b : B, ∃ g : K, (g : G) ∈ J ∧
      h.action (inclusion le_sup_left g) = b.val.val)
    (hsecond : ∀ b : B, ∃ g : L, (g : G) ∈ J ∧
      h'.action (inclusion le_sup_left g) = b.val.val)
    (hexchange : ∃ t ∈ J,
      (three.map h.borelMap).map (MulAut.conj t).toMonoidHom = three.map h'.borelMap) :
    let E₀ := three.map h.borelMap ⊔ three.map h'.borelMap
    let Z₀ := line.map h.borelMap ⊔ line.map h'.borelMap
    Nat.card E₀ = 64 ∧ Nat.card Z₀ = 4 ∧
      (∀ W : Subgroup G, Z₀ ≤ W → W ≤ E₀ → J ≤ normalizer (W : Set G) →
        W = Z₀ ∨ W = E₀) ∧
      (∀ F : Subgroup G, Z₀ ≤ F → J ≤ normalizer (F : Set G) →
        ¬ E₀ ⊓ F ≤ Z₀ → E₀ ≤ F) := by
  let d := h.pairedBorelCoordinates h' J hfirst hsecond hexchange
  have hE : d.six = three.map h.borelMap ⊔ three.map h'.borelMap :=
    h.borelPairMap_prod h' three three
  have hZ : d.two = line.map h.borelMap ⊔ line.map h'.borelMap :=
    h.borelPairMap_prod h' line line
  dsimp only
  rw [← hE, ← hZ]
  exact ⟨d.cards.1, d.cards.2, d.irreducible_interval, d.six_le_of_normalized_intersection⟩

theorem AlternatingPairSetup.paired_borel_irreducible_section
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (J : Subgroup G)
    (hfirst : ∀ b : B, ∃ g : K, (g : G) ∈ J ∧
      h.action (inclusion le_sup_left g) = b.val.val)
    (hsecond : ∀ b : B, ∃ g : L, (g : G) ∈ J ∧
      h'.action (inclusion le_sup_left g) = b.val.val)
    (hexchange : ∃ t ∈ J,
      (three.map h.borelMap).map (MulAut.conj t).toMonoidHom = three.map h'.borelMap) :
    Stellmacher.IsIrreducibleSection J
      (line.map h.borelMap ⊔ line.map h'.borelMap)
      (three.map h.borelMap ⊔ three.map h'.borelMap) := by
  have hg := h.paired_borel_geometry h' J hfirst hsecond hexchange
  refine ⟨sup_le_sup (map_mono line_le_three) (map_mono line_le_three), ?_, ?_⟩
  · intro he
    have hc := congrArg (fun U : Subgroup G => Nat.card U) he
    rw [hg.1, hg.2.1] at hc
    omega
  · intro W hZ hE hi
    apply hg.2.2.1 W hZ hE
    intro g hgJ
    apply mem_normalizer_iff.mpr
    intro w
    constructor
    · exact hi ⟨g, hgJ⟩ w
    · intro hw
      have hh := hi ⟨g⁻¹, J.inv_mem hgJ⟩ (g * w * g⁻¹) hw
      simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right,
        inv_mul_cancel, mul_one] using hh

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
