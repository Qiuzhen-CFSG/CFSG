module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.Cases
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.Action
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.Selection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankInequality
public import Theory.GroupTheory.QuotientIntersection

/-!
# Minimality for both conjugate natural-eight actions

This is the conditional paired-minimality step in the proof of 15.3.25.
`Configuration` anchors U to the actual commutator module U_L, V to U_L's
conjugate, J to XS, and P to O₂(J). It retains conjugation invariance, relative
normality, the natural module coordinates, the actual centralizer kernels,
and the quotient product in 15.3.32(6). `joint_kernel` and `core_factors`
identify that product as the two commuting disjoint factors in J/C_J(UV).

Choose an equal-weight minimal best offender E inside the second action image.
B.2.8 supplies the actual replacement R = B₀ C_V(B₀), where B₀ is the preimage
of E in A. Commutation of U and V gives f(R) = f(B₀) ≤ f(A), and minimality
of f(A) makes these images equal. The replacement witness records both action
images, containment B₀ ≤ A, and the equality of the maximum subgroup orders.

To close the remaining minimality gap, apply the proved paired maximum-order
inequality with the second action as quotient map. If that action were weak,
f(A) ∩ f(ker g) would be an offender inside f(P). Selecting a minimal best
offender there contradicts the exclusion of the four concrete cases from f(P).
Thus the nontrivial maximum images for g are strong; the concrete S8 calculation
gives rank four for each. Containment between two such images is equality.
This proves minimality for the original A, without inferring ambient containment
from an arbitrary minimal-image selection. The established selection theorem
then gives the four cases for both images and their actual fixed codimensions.

The exact remaining inputs for the source-theorem owner are:
* `Configuration`, from the genuine 15.3.32 setup;
* `Lifting` for each restricted action, namely B.2.5's best-offender and
  equal-weight image-lifting clauses;
* `ConstructiveReplacement` for the V-action, namely B.2.8's specific
  B₀ C_V(B₀) membership in the maximum elementary family;
* `NoCaseInCore` for each action: no subgroup realizing any of the four
  concrete cases lies in the corresponding actual image of P.

No source theorem or classification is claimed with those premises undischarged.
The B.2 clauses belong to `qt-b-02-offender-factorization`; the two geometric
exclusions belong to `qt-15-03-char2-paired-quotient`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.4,
printed pp.67–69; B.2.5 and Remark B.2.8, pp.76–77; and the proof of
Theorem 15.3.25 following 15.3.32, pp.1133–1134 (PDF pp.1150–1151).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedMinimality
open Subgroup Stellmacher Representation.BinaryOffender BinaryPermutation
variable {G : Type*} [Group G] [Finite G]

abbrev EightPerm := Equiv.Perm (Fin 8)
noncomputable abbrev eightRepresentation := naturalRepresentation (Fin 8)

/-- The two closure clauses of B.2.5 needed here, without any nonemptiness claim. -/
structure Lifting (S : Subgroup G) (f : G →* EightPerm) : Prop where
  best : ∀ A ∈ elementaryAbelianMaxSubgroups S, A.map f ≠ ⊥ →
    IsBestOffender eightRepresentation (A.map f)
  lift : ∀ A ∈ elementaryAbelianMaxSubgroups S, ∀ E,
    IsElementaryTwo E → EqualWeightLE eightRepresentation E (A.map f) →
    ∃ B ∈ elementaryAbelianMaxSubgroups S, B.map f = E

/-- The preimage in A, not an arbitrary maximum subgroup with a chosen image. -/
def preimage (A : Subgroup G) (g : G →* EightPerm) (E : Subgroup EightPerm) :
    Subgroup G := A ⊓ E.comap g

/-- The actual subgroup B0 C_V(B0) in Remark B.2.8. -/
def replacement (V A : Subgroup G) (g : G →* EightPerm) (E : Subgroup EightPerm) :
    Subgroup G := preimage A g E ⊔ (V ⊓ centralizer (preimage A g E : Set G))

/-- The constructive, equal-weight clause of Remark B.2.8. -/
def ConstructiveReplacement (S V : Subgroup G) (g : G →* EightPerm) : Prop :=
  ∀ A ∈ elementaryAbelianMaxSubgroups S, ∀ E,
    IsElementaryTwo E → EqualWeightLE eightRepresentation E (A.map g) →
    replacement V A g E ∈ elementaryAbelianMaxSubgroups S

/-- The geometric input: none of the four concrete permutation groups lies
in the actual image of the two-core. No rank tuple is assumed. -/
def NoCaseInCore (P : Subgroup G) (f : G →* EightPerm) : Prop :=
  ∀ (E : Subgroup EightPerm) (c : EightCase), c.Realizes E → ¬ E ≤ P.map f

/-- The quotient product in 15.3.32(6). The joint action's kernel is identified
with C_J(UV) below; this is a quotient identity, not an ambient direct product. -/
def CoreProduct (S P : Subgroup G) (f g : G →* EightPerm) : Prop :=
  (f.prod g).ker ≤ P ∧
  let q := QuotientGroup.mk' (f.prod g).ker
  P.map q = (S ⊓ f.ker).map q ⊔ (S ⊓ g.ker).map q

omit [Finite G] in
private theorem kernels_le_core {S P : Subgroup G} {f g : G →* EightPerm}
    (h : CoreProduct S P f g) (hf : f.ker ≤ S) (hg : g.ker ≤ S) :
    f.ker ≤ P ∧ g.ker ≤ P := by
  have hq : (QuotientGroup.mk' (f.prod g).ker).ker ≤ P := by
    simpa only [QuotientGroup.ker_mk'] using h.1
  constructor
  · have hm : f.ker.map (QuotientGroup.mk' (f.prod g).ker) ≤
        P.map (QuotientGroup.mk' (f.prod g).ker) := by
      rw [h.2, inf_eq_right.mpr hf]
      exact le_sup_left
    simpa only [sup_eq_left.mpr hq] using map_le_map_iff.mp hm
  · have hm : g.ker.map (QuotientGroup.mk' (f.prod g).ker) ≤
        P.map (QuotientGroup.mk' (f.prod g).ker) := by
      rw [h.2, inf_eq_right.mpr hg]
      exact le_sup_right
    simpa only [sup_eq_left.mpr hq] using map_le_map_iff.mp hm

private theorem codim_mono {E F : Subgroup EightPerm} (h : E ≤ F) :
    fixedCodim eightRepresentation E ≤ fixedCodim eightRepresentation F := by
  have hfix : fixedSpace eightRepresentation F ≤ fixedSpace eightRepresentation E := by
    intro v hv e
    exact hv ⟨e, h e.property⟩
  have hd := Submodule.finrank_mono hfix
  have hE := fixedCodim_add_finrank eightRepresentation E
  have hF := fixedCodim_add_finrank eightRepresentation F
  omega

private theorem best_codim_pos {E : Subgroup EightPerm}
    (h : IsBestOffender eightRepresentation E) : 0 < fixedCodim eightRepresentation E := by
  obtain ⟨B, hB, hBE⟩ := h.exists_minimal eightRepresentation
  obtain ⟨c, hc⟩ := minimalBest_realizes hB
  have hmono := codim_mono hBE.1
  have hdim := (EightCase.dimensions hc).2
  have hpos : 0 < c.codim := by cases c <;> decide
  exact lt_of_lt_of_le (hdim.symm ▸ hpos) hmono

omit [Finite G] in
private theorem no_offender_in_core {P : Subgroup G} {f : G →* EightPerm}
    (h : NoCaseInCore P f) {E : Subgroup EightPerm} (hE : E ≤ P.map f) :
    ¬ IsOffender eightRepresentation E := by
  intro hEO
  obtain ⟨B, hBE, hB⟩ := hEO.exists_bestOffender eightRepresentation
  obtain ⟨D, hD, hDB⟩ := hB.exists_minimal eightRepresentation
  obtain ⟨c, hc⟩ := minimalBest_realizes hD
  exact h D c hc (hDB.1.trans (hBE.trans hE))

omit [Finite G] in
private theorem image_ne_of_other {S P A : Subgroup G} {f g : G →* EightPerm}
    (hA : A ∈ elementaryAbelianMaxSubgroups S) (hl : Lifting S g)
    (hne : A.map g ≠ ⊥) (hno : NoCaseInCore P g) (hfP : f.ker ≤ P) :
    A.map f ≠ ⊥ := by
  intro he
  have hAP : A ≤ P := ((Subgroup.map_eq_bot_iff _).mp he).trans hfP
  exact no_offender_in_core hno (map_mono hAP)
    ((hl.best A hA hne).isOffender eightRepresentation)

/-- This maximum-order comparison closes the gap between image selection and
ambient containment. A weak g-image would force an f-offender inside f(P). -/
private theorem strong_of_paired_max
    (S U V P A : Subgroup G) [U.Normal] [V.Normal]
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hUS : U ≤ S) (hVS : V ≤ S) (hc : V ≤ centralizer (U : Set G))
    (hd : Disjoint U V) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (f g : G →* EightPerm) (hf : f.ker = centralizer (U : Set G))
    (hg : g.ker = centralizer (V : Set G)) (hgP : g.ker ≤ P)
    (hno : NoCaseInCore P f)
    (hbf : IsBestOffender eightRepresentation (A.map f))
    (hbg : IsBestOffender eightRepresentation (A.map g))
    (hfd : fixedCodim eightRepresentation (A.map f) =
      rank U - rank (U ⊓ centralizer (A : Set G)))
    (hgd : fixedCodim eightRepresentation (A.map g) =
      rank V - rank (V ⊓ centralizer (A : Set G))) :
    IsStrongOffender eightRepresentation (A.map g) := by
  refine ⟨hbg.1, ?_⟩
  by_contra hn
  have heq : fixedCodim eightRepresentation (A.map g) = rank (A.map g) :=
    le_antisymm (hbg.isOffender eightRepresentation).2 (Nat.le_of_not_gt hn)
  have hbound := paired_offender_rank_inequality S U V A hUS hVS hc hd hA g f g hf hg
  have hbot : (A ⊓ g.ker).map g = ⊥ := (Subgroup.map_eq_bot_iff _).mpr inf_le_right
  rw [hbot, Representation.BinaryOffender.rank_bot, add_zero, ← hfd, ← hgd, heq] at hbound
  let E := A.map f ⊓ g.ker.map f
  have hEF : E ≤ A.map f := inf_le_left
  have hEP : E ≤ P.map f := inf_le_right.trans (map_mono hgP)
  have hpos := best_codim_pos hbf
  have hne : E ≠ ⊥ := by
    intro he
    change _ ≤ _ + rank E at hbound
    rw [he, Representation.BinaryOffender.rank_bot, add_zero] at hbound
    omega
  apply no_offender_in_core hno hEP
  refine ⟨hbf.1.of_le hEF hne, ?_⟩
  have hm := codim_mono hEF
  change _ ≤ _ + rank E at hbound
  omega

private theorem strong_rank {E : Subgroup EightPerm}
    (h : IsStrongOffender eightRepresentation E) : rank E = 4 := by
  exact (EightCase.dimensions (c := .disjoint)
    ((CFSG.Quasithin.ChapterB.Offenders.Eight.isStrongOffender_natural_iff E).mp h)).1

omit [Finite G] in
private theorem preimage_image {A : Subgroup G} {g : G →* EightPerm}
    {E : Subgroup EightPerm} (hEA : E ≤ A.map g) : (preimage A g E).map g = E := by
  apply le_antisymm
  · rintro x ⟨a, ha, rfl⟩
    exact ha.2
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hEA hx
    exact ⟨a, ⟨ha, hx⟩, rfl⟩

omit [Finite G] in
private theorem replacement_images {V A : Subgroup G} {f g : G →* EightPerm}
    {E : Subgroup EightPerm} (hEA : E ≤ A.map g)
    (hVf : V ≤ f.ker) (hVg : V ≤ g.ker) :
    (replacement V A g E).map f = (preimage A g E).map f ∧
      (replacement V A g E).map g = E := by
  have hf : (V ⊓ centralizer (preimage A g E : Set G)).map f = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (inf_le_left.trans hVf)
  have hg : (V ⊓ centralizer (preimage A g E : Set G)).map g = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (inf_le_left.trans hVg)
  simp only [replacement, Subgroup.map_sup, hf, hg, sup_bot_eq, preimage_image hEA, and_self]


/-- A constructive witness, including both images of B0 and of B0 C_V(B0).
The equality of E with the original g-image is a proved output. -/
structure ReplacementWitness (S V A : Subgroup G) (f g : G →* EightPerm) where
  image : Subgroup EightPerm
  minimal : IsMinimalBestOffender eightRepresentation image
  equalWeight : EqualWeightLE eightRepresentation image (A.map g)
  preimage_le : preimage A g image ≤ A
  preimage_f : (preimage A g image).map f = A.map f
  preimage_g : (preimage A g image).map g = image
  replacement_max : replacement V A g image ∈ elementaryAbelianMaxSubgroups S
  replacement_card : Nat.card (replacement V A g image) = Nat.card A
  replacement_f : (replacement V A g image).map f = A.map f
  replacement_g : (replacement V A g image).map g = image
  image_eq : image = A.map g

private theorem transfer
    (S U V P A : Subgroup G) [U.Normal] [V.Normal]
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hUS : U ≤ S) (hVS : V ≤ S) (hc : V ≤ centralizer (U : Set G))
    (hd : Disjoint U V) (f g : G →* EightPerm)
    (hf : f.ker = centralizer (U : Set G))
    (hg : g.ker = centralizer (V : Set G)) (hfS : f.ker ≤ S) (hgS : g.ker ≤ S)
    (hcore : CoreProduct S P f g)
    (hfd : ∀ B : Subgroup G, fixedCodim eightRepresentation (B.map f) =
      rank U - rank (U ⊓ centralizer (B : Set G)))
    (hgd : ∀ B : Subgroup G, fixedCodim eightRepresentation (B.map g) =
      rank V - rank (V ⊓ centralizer (B : Set G)))
    (lf : Lifting S f) (lg : Lifting S g) (lr : ConstructiveReplacement S V g)
    (nf : NoCaseInCore P f) (ng : NoCaseInCore P g)
    (hA : A ∈ minimalNontrivialActionFamily S f) :
    A ∈ minimalNontrivialActionFamily S g ∧ Nonempty (ReplacementWitness S V A f g) := by
  obtain ⟨hfP, hgP⟩ := kernels_le_core hcore hfS hgS
  have hAn : A.map g ≠ ⊥ := image_ne_of_other hA.1 lf hA.2.1.1 nf hgP
  have hAbest := lg.best A hA.1 hAn
  obtain ⟨E, hE, hEA⟩ := hAbest.exists_minimal eightRepresentation
  let B0 := preimage A g E
  let R := replacement V A g E
  have hR : R ∈ elementaryAbelianMaxSubgroups S := lr A hA.1 E hE.1.1 hEA
  have hVf : V ≤ f.ker := hf ▸ hc
  have hVg : V ≤ g.ker := hg ▸ le_centralizer_iff_isMulCommutative.mpr inferInstance
  obtain ⟨hRf, hRg⟩ := replacement_images hEA.1 hVf hVg
  have hRfn : R.map f ≠ ⊥ := by
    apply image_ne_of_other hR lg _ ng hfP
    exact hRg.symm ▸ hE.1.1.1
  have hRfA : R.map f = A.map f := by
    have hle : R.map f ≤ A.map f := hRf ▸ map_mono (show B0 ≤ A from inf_le_left)
    exact le_antisymm hle (hA.2.2 ⟨hRfn, R, hR, rfl⟩ hle)
  have allStrong (B : Subgroup G) (hB : B ∈ elementaryAbelianMaxSubgroups S)
      (hn : B.map g ≠ ⊥) : IsStrongOffender eightRepresentation (B.map g) := by
    have hnF := image_ne_of_other hB lg hn ng hfP
    exact strong_of_paired_max S U V P B hUS hVS hc hd hB f g hf hg hgP nf
      (lf.best B hB hnF) (lg.best B hB hn) (hfd B) (hgd B)
  have hsA := allStrong A hA.1 hAn
  have hAg : A ∈ minimalNontrivialActionFamily S g := by
    refine ⟨hA.1, ⟨hAn, A, hA.1, rfl⟩, ?_⟩
    rintro D ⟨hDn, B, hB, rfl⟩ hBA
    have hsB := allStrong B hB hDn
    have hcard : Nat.card (A.map g) = Nat.card (B.map g) := by
      rw [hsA.1.card_eq_two_pow_rank, hsB.1.card_eq_two_pow_rank,
        strong_rank hsA, strong_rank hsB]
    exact (eq_of_le_of_card_ge hBA hcard.le).ge
  have hEeq : E = A.map g := by
    apply le_antisymm hEA.1
    exact hAg.2.2 ⟨hE.1.1.1, R, hR, hRg⟩ hEA.1
  have hRcard : Nat.card R = Nat.card A :=
    (maxOrder_eq_card_of_mem S R hR).symm.trans (maxOrder_eq_card_of_mem S A hA.1)
  exact ⟨hAg, ⟨⟨E, hE, hEA, inf_le_left, hRf.symm.trans hRfA,
    preimage_image hEA.1, hR, hRcard, hRfA, hRg, hEeq⟩⟩⟩


/-- The genuine portion of 15.3.32 used by paired minimality. U is the actual
commutator module, V its actual conjugate, and J = XS. Normality is inside J.
The kernels and quotient product are assumptions from that configuration,
not consequences of a bare family label or of arbitrary natural coordinates. -/
structure Configuration (d : LocalData G) (I L X : Subgroup G) (t : G) where
  t_mem : t ∈ (d.T : Subgroup G)
  t_outside : t ∉ d.S
  preserves_S : d.S.conjBy t = d.S
  preserves_J : (X ⊔ d.S).conjBy t = X ⊔ d.S
  preserves_P : ((X ⊔ d.S).pCoreIn 2).conjBy t = (X ⊔ d.S).pCoreIn 2
  local_le : X ⊔ d.S ≤ I
  local_le_conjugate : X ⊔ d.S ≤ I.conjBy t
  first_le : d.componentModule I L ≤ d.S
  second_le : (d.componentModule I L).conjBy t ≤ d.S
  first_normal : ((d.componentModule I L).subgroupOf (X ⊔ d.S)).Normal
  second_normal : (((d.componentModule I L).conjBy t).subgroupOf (X ⊔ d.S)).Normal
  first_elementary : IsElementaryAbelian 2 ((d.componentModule I L).subgroupOf (X ⊔ d.S))
  second_elementary : IsElementaryAbelian 2
    (((d.componentModule I L).conjBy t).subgroupOf (X ⊔ d.S))
  commutes : ((d.componentModule I L).conjBy t).subgroupOf (X ⊔ d.S) ≤
    centralizer ((d.componentModule I L).subgroupOf (X ⊔ d.S) : Set ↥(X ⊔ d.S))
  disjoint : Disjoint ((d.componentModule I L).subgroupOf (X ⊔ d.S))
    (((d.componentModule I L).conjBy t).subgroupOf (X ⊔ d.S))
  action : NaturalEightAction I (d.componentModule I L)
  conjugateAction : NaturalEightAction (I.conjBy t) ((d.componentModule I L).conjBy t)
  first_kernel : (action.restrictActor (X ⊔ d.S) local_le).ker =
    centralizer ((d.componentModule I L).subgroupOf (X ⊔ d.S) : Set ↥(X ⊔ d.S))
  second_kernel : (conjugateAction.restrictActor (X ⊔ d.S) local_le_conjugate).ker =
    centralizer (((d.componentModule I L).conjBy t).subgroupOf (X ⊔ d.S) : Set ↥(X ⊔ d.S))
  first_kernel_le : (action.restrictActor (X ⊔ d.S) local_le).ker ≤ d.S.subgroupOf (X ⊔ d.S)
  second_kernel_le : (conjugateAction.restrictActor (X ⊔ d.S) local_le_conjugate).ker ≤
    d.S.subgroupOf (X ⊔ d.S)
  core_product : CoreProduct (d.S.subgroupOf (X ⊔ d.S)) (pCore 2 ↥(X ⊔ d.S))
    (action.restrictActor (X ⊔ d.S) local_le)
    (conjugateAction.restrictActor (X ⊔ d.S) local_le_conjugate)

namespace Configuration
variable {d : LocalData G} {I L X : Subgroup G} {t : G}

abbrev J (_c : Configuration d I L X t) : Subgroup G := X ⊔ d.S
abbrev S (c : Configuration d I L X t) : Subgroup c.J := d.S.subgroupOf c.J
abbrev U (c : Configuration d I L X t) : Subgroup c.J := (d.componentModule I L).subgroupOf c.J
abbrev V (c : Configuration d I L X t) : Subgroup c.J :=
  ((d.componentModule I L).conjBy t).subgroupOf c.J
noncomputable abbrev P (c : Configuration d I L X t) : Subgroup c.J := pCore 2 c.J
abbrev f (c : Configuration d I L X t) : c.J →* EightPerm :=
  c.action.restrictActor c.J c.local_le
abbrev g (c : Configuration d I L X t) : c.J →* EightPerm :=
  c.conjugateAction.restrictActor c.J c.local_le_conjugate

omit [Finite G] in
/-- The quotient in CoreProduct really is J/C_J(UV). -/
theorem joint_kernel (c : Configuration d I L X t) :
    (c.f.prod c.g).ker = centralizer ((c.U ⊔ c.V : Subgroup c.J) : Set c.J) := by
  let _ := c.second_normal
  rw [MonoidHom.ker_prod, c.first_kernel, c.second_kernel]
  ext x
  constructor
  · intro hx
    apply mem_centralizer_iff.mpr
    intro w hw
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_normal_right.mp hw
    rw [mul_assoc, hx.2 v hv, ← mul_assoc, hx.1 u hu, mul_assoc]
  · intro hx
    exact ⟨fun u hu => hx u (mem_sup_left hu), fun v hv => hx v (mem_sup_right hv)⟩

omit [Finite G] in
/-- Both quotient factors are disjoint and commute. Together with core_product,
this retains the full direct-product identity, not merely generation. -/
theorem core_factors (c : Configuration d I L X t) :
    let q := QuotientGroup.mk' (c.f.prod c.g).ker
    Disjoint ((c.S ⊓ c.f.ker).map q) ((c.S ⊓ c.g.ker).map q) ∧
      (c.S ⊓ c.f.ker).map q ≤ centralizer ((c.S ⊓ c.g.ker).map q : Set _) := by
  dsimp only
  rw [inf_eq_right.mpr c.first_kernel_le, inf_eq_right.mpr c.second_kernel_le]
  let q := QuotientGroup.mk' (c.f.prod c.g).ker
  have hq : q.ker = c.f.ker ⊓ c.g.ker := by
    rw [QuotientGroup.ker_mk', MonoidHom.ker_prod]
  constructor
  · rw [disjoint_iff, ← map_inf_of_ker_le q c.f.ker c.g.ker (hq ▸ inf_le_right)]
    exact (Subgroup.map_eq_bot_iff _).mpr hq.ge
  · apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (hq ▸ commutator_le_inf _ _)

/-- Conditional paired minimality with an explicit, contained preimage B0
and its maximum-order replacement. All B.2 and core-geometry inputs remain
visible for the source-theorem owner to discharge. -/
theorem paired_minimality_with_replacement (c : Configuration d I L X t)
    (lf : Lifting c.S c.f) (lg : Lifting c.S c.g)
    (lr : ConstructiveReplacement c.S c.V c.g)
    (nf : NoCaseInCore c.P c.f) (ng : NoCaseInCore c.P c.g)
    (A : Subgroup c.J) (hA : A ∈ minimalNontrivialActionFamily c.S c.f) :
    A ∈ minimalNontrivialActionFamily c.S c.g ∧
      Nonempty (ReplacementWitness c.S c.V A c.f c.g) := by
  let _ := c.first_normal
  let _ := c.second_normal
  let _ := c.first_elementary
  let _ := c.second_elementary
  exact transfer c.S c.U c.V c.P A
    (fun _ h => c.first_le h) (fun _ h => c.second_le h) c.commutes c.disjoint
    c.f c.g c.first_kernel c.second_kernel c.first_kernel_le c.second_kernel_le c.core_product
    (fun B => c.action.fixedCodim_restrict c.J c.local_le (c.first_le.trans le_sup_right) B)
    (fun B => c.conjugateAction.fixedCodim_restrict c.J c.local_le_conjugate
      (c.second_le.trans le_sup_right) B)
    lf lg lr nf ng hA

/-- Both actual permutation images have the four source geometries, with
ranks and centralizer codimensions computed from those geometries. -/
theorem paired_minimality_and_cases (c : Configuration d I L X t)
    (lf : Lifting c.S c.f) (lg : Lifting c.S c.g)
    (lr : ConstructiveReplacement c.S c.V c.g)
    (nf : NoCaseInCore c.P c.f) (ng : NoCaseInCore c.P c.g)
    (A : Subgroup c.J) (hA : A ∈ minimalNontrivialActionFamily c.S c.f) :
    A ∈ minimalNontrivialActionFamily c.S c.g ∧
    ∃ a b : EightCase, a.Realizes (A.map c.f) ∧ b.Realizes (A.map c.g) ∧
      rank (A.map c.f) = a.actorRank ∧ rank (A.map c.g) = b.actorRank ∧
      rank c.U - rank (c.U ⊓ centralizer (A : Set c.J)) = a.codim ∧
      rank c.V - rank (c.V ⊓ centralizer (A : Set c.J)) = b.codim := by
  have hAg := (c.paired_minimality_with_replacement lf lg lr nf ng A hA).1
  obtain ⟨a, ha⟩ := minimalBest_realizes
    (minimal_action_image_isMinimalBest c.S A c.f eightRepresentation hA lf.best lf.lift)
  obtain ⟨b, hb⟩ := minimalBest_realizes
    (minimal_action_image_isMinimalBest c.S A c.g eightRepresentation hAg lg.best lg.lift)
  have hda := EightCase.dimensions ha
  have hdb := EightCase.dimensions hb
  exact ⟨hAg, a, b, ha, hb, hda.1, hdb.1,
    (c.action.fixedCodim_restrict c.J c.local_le (c.first_le.trans le_sup_right) A).symm.trans hda.2,
    (c.conjugateAction.fixedCodim_restrict c.J c.local_le_conjugate
      (c.second_le.trans le_sup_right) A).symm.trans hdb.2⟩

end Configuration

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedMinimality
end
