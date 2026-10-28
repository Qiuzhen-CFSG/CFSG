module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Coordinates
public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Faithful component coordinates over the star quotient

Let `(I,G₁,G₂)` be the genuine Goldschmidt triple from the mixed setup,
let `L` be its selected component, and suppose `L ≃ A₆`. Given an actual
equivalence `I/O_{3′}(I) ≃ S₆`, this module constructs all the remaining
fields of `QuotientCoordinates L`, keeping exactly that equivalence.

Simplicity and divisibility by three make the quotient faithful on `L`.
Perfectness puts its image in the alternating subgroup, and equality of
orders makes the image all of `A₆`. Distinct components cannot have the
same nontrivial image, so every conjugate of `L` equals `L`.

The kernel argument uses generation by the two original local groups.
The quotient by `L` has order `2 |O_{3′}(I)|`, prime to three. Each local
group has order `3` times a power of two, by its actual `S₃` quotient over
its two-core. Its image modulo `L` is therefore a two-group, hence equals
the image of the common Sylow subgroup. Those images generate `I/L`, so
`I/L` is a two-group. Faithfulness embeds `O_{3′}(I)` into `I/L`.

Thus the genuine Goldschmidt triple already suffices for this step of the
raw mixed setup. No local splitting, factor containment, or centralizer
index is required. Construction of the supplied whole-quotient equivalence
and final raw-to-local assembly remain with their respective owners.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Definition F.6.1, printed p.304, and the component
paragraph of 15.4.18, printed pp.1162–1163.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.KernelCoordinates

variable {I : Type*} [Group I] {L : Subgroup I}

/-- The actual star quotient map followed by the supplied model equivalence. -/
def starMap (e : (I ⧸ pPrimeCore 3 I) ≃* S6) : I →* S6 :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 3 I))

/-- Changing coordinates on the quotient preserves its actual kernel. -/
theorem starMap_ker (e : (I ⧸ pPrimeCore 3 I) ≃* S6) :
    (starMap e).ker = pPrimeCore 3 I := by
  rw [starMap, MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

variable [Finite I]

/-- The simple `A₆` subgroup meets the three-prime core trivially. -/
theorem component_faithful (a : L ≃* A6) (e : (I ⧸ pPrimeCore 3 I) ≃* S6) :
    Function.Injective ((starMap e).comp L.subtype) := by
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup L := (MulEquiv.isSimpleGroup_congr a).mpr inferInstance
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : (((starMap e).comp L.subtype).ker).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hle : L ≤ pPrimeCore 3 I := by
      intro l hl
      have hh : starMap e l = 1 :=
        show (⟨l, hl⟩ : L) ∈ ((starMap e).comp L.subtype).ker from h ▸ mem_top _
      rw [← starMap_ker e]
      exact hh
    have hc : Nat.card L = 360 := (Nat.card_congr a.toEquiv).trans a6_order
    have hd : 3 ∣ Nat.card (pPrimeCore 3 I) :=
      (hc ▸ (by decide : 3 ∣ 360)).trans (card_dvd_of_le hle)
    exact ((Nat.prime_three.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (p := 3))) hd).elim

/-- The faithful component image is the actual alternating subgroup of `S₆`. -/
theorem component_image (hL : IsComponent I L) (a : L ≃* A6)
    (e : (I ⧸ pPrimeCore 3 I) ≃* S6) : L.map (starMap e) = A6 := by
  let := hL.2
  have hle : L.map (starMap e) ≤ A6 := by
    rw [← L.commutator_eq_self, map_commutator]
    exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
  apply eq_of_le_of_card_ge hle
  let b : L ≃* L.map (starMap e) := MulEquiv.ofBijective ((starMap e).subgroupMap L)
    ⟨fun _ _ h => component_faithful a e (congrArg Subtype.val h),
      (starMap e).subgroupMap_surjective L⟩
  exact (Nat.card_congr (b.symm.trans a).toEquiv).symm.le

/-- Normality is proved inside `I`: conjugate components have the same
nontrivial alternating image and must coincide. -/
theorem component_normal (hL : IsComponent I L) (a : L ≃* A6)
    (e : (I ⧸ pPrimeCore 3 I) ≃* S6) : L.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hm : (L.map (MulAut.conj g).toMonoidHom).map (starMap e) =
      L.map (starMap e) := by
    have hc : (starMap e).comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (starMap e g)).toMonoidHom.comp (starMap e) := by
      ext x
      simp [MulAut.conj_apply]
    rw [map_map, hc, ← map_map, component_image hL a e]
    exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; trivial)
  apply (hL.map_conj g).eq_of_map_eq hL (starMap e) hm
  rw [hm, component_image hL a e]
  intro h
  have hh := congrArg (fun H : Subgroup S6 => Nat.card H) h
  change Nat.card A6 = Nat.card (⊥ : Subgroup S6) at hh
  rw [a6_order, card_bot] at hh
  omega

omit [Finite I] in
private theorem quotient_card (a : L ≃* A6)
    (e : (I ⧸ pPrimeCore 3 I) ≃* S6) [L.Normal] :
    Nat.card (I ⧸ L) = 2 * Nat.card (pPrimeCore 3 I) := by
  have hI := card_eq_card_quotient_mul_card_subgroup (pPrimeCore 3 I)
  have hC := card_eq_card_quotient_mul_card_subgroup L
  rw [Nat.card_congr e.toEquiv, s6_order] at hI
  rw [Nat.card_congr a.toEquiv, a6_order] at hC
  omega

private theorem local_image_two {D : Type*} [Group D] [Finite D] (f : I →* D)
    (hc : Nat.Coprime 3 (Nat.card D)) (A : Subgroup I)
    (a : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) : IsPGroup 2 (A.map f) := by
  have hA := card_eq_card_quotient_mul_card_subgroup (pCore 2 A)
  have hS : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [Nat.card_congr a.toEquiv, hS] at hA
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := A))
  rw [hn] at hA
  have hd : Nat.card (A.map f) ∣ 3 * 2 ^ (n + 1) := by
    have he : 6 * 2 ^ n = 3 * 2 ^ (n + 1) := by rw [pow_succ]; ring
    exact (A.card_map_dvd f).trans (hA.trans he).dvd
  apply IsPGroup.of_card_dvd_pow
  exact (hc.of_dvd_right (A.map f).card_subgroup_dvd_card).symm.dvd_of_dvd_mul_left hd

private theorem quotient_two {A B : Subgroup I} (h : ChapterF.IsGoldschmidtTriple A B)
    (N : Subgroup I) [N.Normal] (hc : Nat.Coprime 3 (Nat.card (I ⧸ N))) :
    IsPGroup 2 (I ⧸ N) := by
  let f := QuotientGroup.mk' N
  obtain ⟨P, hP⟩ := h.intersection_sylow
  let Q : Sylow 2 (I ⧸ N) := P.mapSurjective (QuotientGroup.mk'_surjective N)
  have hA : A.map f = (Q : Subgroup (I ⧸ N)) := by
    obtain ⟨a⟩ := h.quotient_left
    exact Q.is_maximal' (local_image_two f hc A a)
      (map_mono (hP.symm.le.trans inf_le_left))
  have hB : B.map f = (Q : Subgroup (I ⧸ N)) := by
    obtain ⟨b⟩ := h.quotient_right
    exact Q.is_maximal' (local_image_two f hc B b)
      (map_mono (hP.symm.le.trans inf_le_right))
  have ht : (Q : Subgroup (I ⧸ N)) = ⊤ := by
    have hm := congrArg (Subgroup.map f) h.generated
    rw [Subgroup.map_sup, hA, hB, sup_idem, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)] at hm
    exact hm
  exact (ht ▸ Q.isPGroup').of_equiv Subgroup.topEquiv

/-- Generation by the genuine local groups makes the star kernel a two-group.
This does not infer the claim from trivial odd core or two-closedness. -/
theorem kernel_isTwoGroup {A B : Subgroup I} (h : ChapterF.IsGoldschmidtTriple A B)
    (hL : IsComponent I L) (a : L ≃* A6)
    (e : (I ⧸ pPrimeCore 3 I) ≃* S6) : IsPGroup 2 (pPrimeCore 3 I) := by
  let : L.Normal := component_normal hL a e
  have hc : Nat.Coprime 3 (Nat.card (I ⧸ L)) := by
    rw [quotient_card a e]
    exact (by decide : Nat.Coprime 3 2).mul_right (pPrimeCore_coprime_card (p := 3))
  let f := (QuotientGroup.mk' L).comp (pPrimeCore 3 I).subtype
  apply (quotient_two h L hc).of_injective f
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_bot_iff.mp
  intro r hr
  have hrL : (r : I) ∈ L := (QuotientGroup.eq_one_iff _).mp hr
  have hrq : starMap e (r : I) = 1 := by
    change (r : I) ∈ (starMap e).ker
    rw [starMap_ker e]
    exact r.property
  have heq : (⟨(r : I), hrL⟩ : L) = 1 := component_faithful a e (by simpa using hrq)
  have heq' : (r : I) = 1 := congrArg (fun l : L => (l : I)) heq
  exact mem_bot.mpr (Subtype.ext heq')

/-- Construct compatible coordinates from the genuine triple, selected actual
component, and the supplied equivalence of the whole star quotient. -/
def ofGoldschmidtTriple {A B : Subgroup I} (h : ChapterF.IsGoldschmidtTriple A B)
    (hL : IsComponent I L) (a : L ≃* A6)
    (e : (I ⧸ pPrimeCore 3 I) ≃* S6) : QuotientCoordinates L where
  equiv := e
  component_normal := component_normal hL a e
  component_image := component_image hL a e
  component_faithful := component_faithful a e
  kernel_two := kernel_isTwoGroup h hL a e

/-- The construction preserves the given quotient equivalence exactly. -/
theorem ofGoldschmidtTriple_equiv {A B : Subgroup I} (h : ChapterF.IsGoldschmidtTriple A B)
    (hL : IsComponent I L) (a : L ≃* A6) (e : (I ⧸ pPrimeCore 3 I) ≃* S6) :
    (ofGoldschmidtTriple h hL a e).equiv = e := rfl

/-- Its coordinate map is still the original quotient followed by `e`. -/
theorem ofGoldschmidtTriple_quotientMap {A B : Subgroup I}
    (h : ChapterF.IsGoldschmidtTriple A B) (hL : IsComponent I L)
    (a : L ≃* A6) (e : (I ⧸ pPrimeCore 3 I) ≃* S6) :
    (ofGoldschmidtTriple h hL a e).quotientMap =
      e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 3 I)) := rfl

/-- The faithful coordinate contract is inhabited, with no further local
recognition or centralizer premises. -/
theorem nonempty_quotientCoordinates {A B : Subgroup I}
    (h : ChapterF.IsGoldschmidtTriple A B) (hL : IsComponent I L)
    (a : L ≃* A6) (e : (I ⧸ pPrimeCore 3 I) ≃* S6) :
    Nonempty (QuotientCoordinates L) := ⟨ofGoldschmidtTriple h hL a e⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.KernelCoordinates
