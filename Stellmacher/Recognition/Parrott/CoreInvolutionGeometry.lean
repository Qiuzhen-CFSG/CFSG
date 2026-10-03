module
public import Stellmacher.Recognition.Parrott.DerivedCentralizer
public import Theory.GroupTheory.ElementaryInvolutionFixedJoin
public import Theory.GroupTheory.CentralCommutatorFixedIndex
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Elementary subgroups from involutions in Parrott's two-core

Put H=C_G(z), J=O₂(H), and let E be the actual ambient image of J'.
For every involution a in J outside E, the literal subgroup
F=⟨a⟩(E∩C_G(a)) is elementary of order 32, distinct from E, and
intersects E in order 16. It lies in the actual image of each Sylow
two-subgroup of H, and E normalizes it.

The equality J'=Z₂(J), the center of order two, and C_G(E)=E make
the commutator map from J' onto Z(J) nontrivial. Its kernel is the
fixed hyperplane of order 16. The elementary fixed-join theorem then
gives the subgroup geometry, transported through the actual inclusions.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.673 property (a), and p.675, the opening of §2. Selection of the
five-coset orbit in Lemma 4 and self-centralization are separate steps.
-/

open Subgroup
open scoped commutatorElement
namespace Stellmacher.Recognition

/-- Every core element outside the derived subgroup fixes exactly sixteen
elements of the derived subgroup. -/
public theorem parrott_core_element_fixed_card
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ a : G, a ∈ J.map H.subtype → a ∉ E →
      Nat.card (E ⊓ centralizer ({a} : Set G) : Subgroup G) = 16 := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let embed : J →* G := H.subtype.comp J.subtype
  let E := D.map embed
  change ∀ a : G, a ∈ J.map H.subtype → a ∉ E → _
  intro a ha haE
  obtain ⟨aH, haJ, rfl⟩ := ha
  let aJ : J := ⟨aH, haJ⟩
  obtain ⟨hZmap, _, _, _, hUpper, _, hDcard, _⟩ := parrott_centralizer_structure z h
  have hZcard : Nat.card (center J) = 2 := by
    have hc := card_map_of_injective (K := center J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)
    rw [hZmap, Nat.card_zpowers, h.involution] at hc
    exact hc.symm
  have hcomm : ⁅D, ⊤⁆ ≤ center J := by
    rw [show D = Subgroup.upperCentralSeries J 2 from hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      commutator_upperCentralSeries_top_le J 1
  have haC : aJ ∉ centralizer (D : Set J) := by
    intro hc
    apply haE
    have hCE : centralizer (E : Set G) = E := parrott_derived_centralizer z h
    rw [← hCE]
    rintro b ⟨d, hd, rfl⟩
    exact congrArg embed (hc d hd)
  have hindex := centralizer_relIndex_eq_two_of_commutator_le_center D hcomm hZcard aJ haC
  let C := (centralizer ({aJ} : Set J)).subgroupOf D
  have hCcard : Nat.card C = 16 := by
    have hc := C.index_mul_card
    change C.index = 2 at hindex
    rw [hindex, hDcard] at hc
    omega
  let f : D →* G := embed.comp D.subtype
  have hinj : Function.Injective f :=
    (H.subtype_injective.comp J.subtype_injective).comp D.subtype_injective
  have hmap : C.map f = E ⊓ centralizer ({(aH : G)} : Set G) := by
    apply le_antisymm
    · rintro b ⟨d, hd, rfl⟩
      refine ⟨mem_map_of_mem embed d.property, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg embed (mem_centralizer_singleton_iff.mp hd)
    · rintro b ⟨⟨d, hd, rfl⟩, hb⟩
      refine ⟨⟨d, hd⟩, ?_, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply H.subtype_injective.comp J.subtype_injective
      exact mem_centralizer_singleton_iff.mp hb
  change Nat.card (E ⊓ centralizer ({(aH : G)} : Set G) : Subgroup G) = 16
  rw [← hmap, card_map_of_injective hinj, hCcard]

/-- The actual fixed join associated to any core involution outside E.
The local and ambient Sylow subgroups are compatible through inclusion. -/
public theorem parrott_core_involution_fixed_join
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ a : G, a ∈ J.map H.subtype → orderOf a = 2 → a ∉ E →
      let Z := E ⊓ centralizer ({a} : Set G)
      let F := zpowers a ⊔ Z
      IsElementaryAbelian 2 F ∧ Nat.card F = 32 ∧
        E ⊓ F = Z ∧ Nat.card Z = 16 ∧ F ≠ E ∧ z ∈ Z ∧
        E ≤ normalizer (F : Set G) ∧ E ⊓ centralizer (F : Set G) = Z ∧
        F ≤ J.map H.subtype ∧
        ∀ T : Sylow 2 H, ∃ S : Sylow 2 G,
          (S : Subgroup G) = (T : Subgroup H).map H.subtype ∧ F ≤ S := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let E := D.map (H.subtype.comp J.subtype)
  change ∀ a : G, a ∈ J.map H.subtype → orderOf a = 2 → a ∉ E → _
  intro a ha ha2 haE
  let Z := E ⊓ centralizer ({a} : Set G)
  let F := zpowers a ⊔ Z
  change IsElementaryAbelian 2 F ∧ Nat.card F = 32 ∧ E ⊓ F = Z ∧
    Nat.card Z = 16 ∧ F ≠ E ∧ z ∈ Z ∧ E ≤ normalizer (F : Set G) ∧
    E ⊓ centralizer (F : Set G) = Z ∧ F ≤ J.map H.subtype ∧ _
  have haH : a ∈ H := map_subtype_le J ha
  let aH : H := ⟨a, haH⟩
  let ZH := DH ⊓ centralizer ({aH} : Set H)
  let FH := zpowers aH ⊔ ZH
  obtain ⟨hcenter, _, _, _, hupper, hElem, _, hSylow⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  let : IsElementaryAbelian 2 DH := IsElementaryAbelian.map J.subtype
  have hDHmap : DH.map H.subtype = E := map_map _ _ _
  have haDH : aH ∉ DH := fun hh => haE (hDHmap ▸ mem_map_of_mem H.subtype hh)
  have haH2 : orderOf aH = 2 := (Subgroup.orderOf_coe aH).symm.trans ha2
  obtain ⟨hFHelem, hENH, hCXH, hEXH, _⟩ :=
    elementary_involution_fixed_join_data DH aH haH2 haDH
  change IsElementaryAbelian 2 FH at hFHelem
  change DH ≤ normalizer (FH : Set H) at hENH
  change DH ⊓ centralizer (FH : Set H) = ZH at hCXH
  change DH ⊓ FH = ZH at hEXH
  have hZmap : ZH.map H.subtype = Z := by
    apply le_antisymm
    · rintro b ⟨c, hc, rfl⟩
      exact ⟨hDHmap ▸ mem_map_of_mem H.subtype hc.1,
        mem_centralizer_singleton_iff.mpr
          (congrArg H.subtype (mem_centralizer_singleton_iff.mp hc.2))⟩
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := hDHmap.symm ▸ hb.1
      refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hb.2))
  have hFmap : FH.map H.subtype = F := by
    change (zpowers aH ⊔ ZH).map H.subtype = F
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hZmap]
    rfl
  have hFelem : IsElementaryAbelian 2 F := by
    rw [← hFmap]
    let : IsElementaryAbelian 2 FH := hFHelem
    exact IsElementaryAbelian.map H.subtype
  let : IsElementaryAbelian 2 F := hFelem
  have hZcard : Nat.card Z = 16 := parrott_core_element_fixed_card z h a ha haE
  have haZ : a ∉ Z := fun hh => haE hh.1
  have haCZ : a ∈ centralizer (Z : Set G) :=
    fun b hb => mem_centralizer_singleton_iff.mp hb.2
  have hFcard : Nat.card F = 32 := by
    change Nat.card (zpowers a ⊔ Z : Subgroup G) = 32
    rw [sup_comm, card_sup_zpowers_of_normalizing_involution Z a
      (ha2 ▸ pow_orderOf_eq_one a) haZ ((centralizer_le_normalizer _) haCZ), hZcard]
  have hEF : E ⊓ F = Z := by
    rw [← hDHmap, ← hFmap, ← Subgroup.map_inf DH FH H.subtype H.subtype_injective,
      hEXH, hZmap]
  have hFne : F ≠ E := by
    intro heq
    exact haE (heq ▸ (show a ∈ F from (le_sup_left : zpowers a ≤ F) (mem_zpowers a)))
  have hzE : z ∈ E := by
    have hzC : z ∈ (center J).map (H.subtype.comp J.subtype) := hcenter.symm ▸ mem_zpowers z
    apply map_mono (show center J ≤ D from ?_) hzC
    rw [show D = Subgroup.upperCentralSeries J 2 from hupper, ← Subgroup.upperCentralSeries_one]
    exact Subgroup.upperCentralSeries_mono J (by decide : 1 ≤ 2)
  have hzZ : z ∈ Z := ⟨hzE, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp haH).symm⟩
  have hEN : E ≤ normalizer (F : Set G) := by
    rw [← hDHmap, ← hFmap]
    exact (map_mono hENH).trans (le_normalizer_map H.subtype)
  have hCF : E ⊓ centralizer (F : Set G) = Z := by
    apply le_antisymm
    · intro b hb
      exact ⟨hb.1, mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hb.2) a ((le_sup_left : zpowers a ≤ F) (mem_zpowers a))).symm⟩
    · intro b hb
      refine ⟨hb.1, ?_⟩
      exact le_centralizer_iff_isMulCommutative.mpr inferInstance
        ((le_sup_right : Z ≤ F) hb)
  have hEJ : E ≤ J.map H.subtype := by
    rw [← hDHmap]
    exact map_mono (map_subtype_le D)
  have hFJ : F ≤ J.map H.subtype := sup_le (zpowers_le.mpr ha) (inf_le_left.trans hEJ)
  refine ⟨hFelem, hFcard, hEF, hZcard, hFne, hzZ, hEN, hCF, hFJ, ?_⟩
  intro T
  obtain ⟨S, hS⟩ := hSylow T
  refine ⟨S, hS, ?_⟩
  rw [hS]
  exact hFJ.trans (map_mono (pCore_isPGroup.le_sylow_of_normal T))

/-- A five-element conjugacy orbit of the core coset gives a compatible
local and ambient Sylow two-subgroup normalizing the fixed join. -/
public theorem parrott_fixed_join_sylow_of_coset_index_five
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let DH := (commutator J).map J.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ a : H, orderOf a = 2 → a ∉ DH →
      (centralizer ({QuotientGroup.mk' DH a} : Set (H ⧸ DH))).index = 5 →
      let F := zpowers (a : G) ⊔ (E ⊓ centralizer ({(a : G)} : Set G))
      ∃ T : Sylow 2 H, ∃ S : Sylow 2 G,
        (S : Subgroup G) = (T : Subgroup H).map H.subtype ∧
        F ≤ S ∧ (S : Subgroup G) ≤ normalizer (F : Set G) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let E := D.map (H.subtype.comp J.subtype)
  change ∀ a : H, orderOf a = 2 → a ∉ DH → _
  intro a ha haDH hindex
  let ZH := DH ⊓ centralizer ({a} : Set H)
  let FH := zpowers a ⊔ ZH
  let F := zpowers (a : G) ⊔ (E ⊓ centralizer ({(a : G)} : Set G))
  let N := normalizer (FH : Set H)
  change ∃ T : Sylow 2 H, ∃ S : Sylow 2 G,
    (S : Subgroup G) = (T : Subgroup H).map H.subtype ∧
    F ≤ S ∧ (S : Subgroup G) ≤ normalizer (F : Set G)
  obtain ⟨_, _, _, _, _, hElem, _, hSylow⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  let : IsElementaryAbelian 2 DH := IsElementaryAbelian.map J.subtype
  have hNindex : N.index = 5 := by
    change (normalizer (FH : Set H)).index = 5
    rw [elementary_involution_fixed_join_normalizer DH a ha haDH,
      index_comap_of_surjective _ (QuotientGroup.mk'_surjective DH)]
    exact hindex
  have hHcard : Nat.card H = 10240 := (h.card_and_solvable z).1
  have hNcard : Nat.card N = 2 ^ 11 := by
    have hc := N.index_mul_card
    rw [hNindex, hHcard] at hc
    omega
  obtain ⟨T, hNT⟩ := (IsPGroup.of_card hNcard).exists_le_sylow
  have hTeq : N = (T : Subgroup H) := by
    apply eq_of_le_of_card_ge hNT
    have hTcard : Nat.card T = 2 ^ 11 := by
      rw [T.card_eq_multiplicity, hHcard]
      decide +kernel
    rw [hNcard, hTcard]
  have hDHmap : DH.map H.subtype = E := map_map _ _ _
  have hZmap : ZH.map H.subtype = E ⊓ centralizer ({(a : G)} : Set G) := by
    apply le_antisymm
    · rintro b ⟨c, hc, rfl⟩
      exact ⟨hDHmap ▸ mem_map_of_mem H.subtype hc.1,
        mem_centralizer_singleton_iff.mpr
          (congrArg H.subtype (mem_centralizer_singleton_iff.mp hc.2))⟩
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := hDHmap.symm ▸ hb.1
      refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hb.2))
  have hFmap : FH.map H.subtype = F := by
    change (zpowers a ⊔ ZH).map H.subtype = F
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hZmap]
    rfl
  obtain ⟨S, hS⟩ := hSylow T
  refine ⟨T, S, hS, ?_, ?_⟩
  · rw [hS, ← hTeq, ← hFmap]
    exact map_mono le_normalizer
  · rw [hS, ← hTeq, ← hFmap]
    exact le_normalizer_map H.subtype

end Stellmacher.Recognition
