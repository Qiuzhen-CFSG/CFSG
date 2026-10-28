module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.B2Lifting
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry
public import Stellmacher.ElementaryAbelianMaxFamilyMap
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Completing the paired S8 offender calculation

Work with the genuine two conjugate modules in `PairedMinimality.Configuration`.
`Geometry` records the compatible parabolic coordinates and conjugation diagrams
on the literal quotient XT/O₂(XT), including the actual GL₂(3) Sylow alternative
and the identification of S₀ = S ∩ LO₂(LS) as the marked even preimage.
It contains no offender, numerical, replacement, or normalization conclusions.

The B.2 inputs are discharged by `B2Lifting`; exclusion from the concrete core
then gives paired minimality and the four actual action geometries. The paired
rank inequality contradicts the semidihedral pairings and all equal cases other
than disjoint transpositions. Its sharp bound constructs W C_A(W) as a maximum
elementary subgroup centralizing U_L. Noncentrality of the component of J(I)
provides a nonempty minimal family, so T has the same quotient image as S and
normalizes the literal S₀. The replacement and minimal-image exclusion give
J(S₀) = J(C_I(U_L)); the earlier uniqueness hypothesis finishes the contradiction.

`Geometry.conclusions` is the conditional offender output requested by the
source assembly owner. `Geometry.outside_contradiction` is its terminal consumer.
The genuine configuration, compatible diagrams, Sylow witness, component
noncentrality and ambient action-kernel identity remain explicit source inputs;
this module does not assert that those configurations have been constructed.
No rank tuples, paired minimality, or B.2 closure clauses remain as premises.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Theorem 15.3.25 after 15.3.32, printed pp.1133–1134 (PDF pp.1150–1151).
-/

@[expose] public section
set_option linter.unusedSectionVars false
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders
open Subgroup Stellmacher Representation.BinaryOffender BinaryPermutation
open PairedMinimality PairedQuotient PairedQuotient.Conjugation
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I L X : Subgroup G} {t : G}

abbrev XT (d : LocalData G) (X : Subgroup G) := X ⊔ (d.T : Subgroup G)
noncomputable abbrev quotientMap (d : LocalData G) (X : Subgroup G) :=
  QuotientGroup.mk' (pCore 2 (XT d X))

namespace Configuration
variable (c : PairedMinimality.Configuration d I L X t)

def toXT (hST : d.S ≤ (d.T : Subgroup G)) : c.J →* XT d X :=
  inclusion (sup_le le_sup_left (hST.trans le_sup_right))
noncomputable abbrev q (hST : d.S ≤ (d.T : Subgroup G)) :=
  (quotientMap d X).comp (toXT c hST)
noncomputable abbrev Timage (_c : PairedMinimality.Configuration d I L X t) : Subgroup (XT d X ⧸ pCore 2 (XT d X)) :=
  ((d.T : Subgroup G).subgroupOf (XT d X)).map (quotientMap d X)
noncomputable abbrev tq : XT d X ⧸ pCore 2 (XT d X) :=
  quotientMap d X ⟨t, (le_sup_right : (d.T : Subgroup G) ≤ XT d X) c.t_mem⟩

theorem Simage_le_Timage (hST : d.S ≤ (d.T : Subgroup G)) :
    c.S.map (q c hST) ≤ Timage c := by
  rintro x ⟨s, hs, rfl⟩
  exact ⟨toXT c hST s, hST hs, rfl⟩

theorem tq_mem_Timage : tq c ∈ Timage c :=
  mem_map_of_mem _ c.t_mem

end Configuration

/-- Only genuine source geometry is retained: the two local action diagrams,
actual core images, conjugation equations, and the GL2(3) quotient alternative.
There are no offender cases, rank bounds, minimality, normalization, or
replacement conclusions among these inputs. -/
structure Geometry (c : PairedMinimality.Configuration d I L X t) where
  s_le_t : d.S ≤ (d.T : Subgroup G)
  first : SylowCoordinates c.S c.f (Configuration.q c s_le_t)
  second : SylowCoordinates c.S c.g (Configuration.q c s_le_t)
  core : (Configuration.q c s_le_t).ker = c.P
  first_core : c.P.map c.f = blockCore
  second_core : c.P.map c.g = blockCore
  actorConj : MulAut c.S
  actorConj_eq : ∀ s : c.S, ((actorConj s : c.J) : G) = t * (s : c.J) * t⁻¹
  quotientConj : MulAut (c.S.map (Configuration.q c s_le_t))
  quotientConj_eq : ∀ x, (quotientConj x : XT d X ⧸ pCore 2 (XT d X)) =
    Configuration.tq c * x * (Configuration.tq c)⁻¹
  relabel : EightPerm
  actionConj : ∀ s, c.g (actorConj s) = relabel * c.f s * relabel⁻¹
  generation : (d.T : Subgroup G) = d.S ⊔ zpowers t
  extension : c.S.map (Configuration.q c s_le_t) ≠ Configuration.Timage c →
    ∃ P : Sylow 2 (GL (Fin 2) (ZMod 3)), Nonempty (Configuration.Timage c ≃* P)
  even_preimage : d.S0 L =
    (((localCoordinates first).marked.map
      (c.S.map (Configuration.q c s_le_t)).subtype).comap
        (quotientMap d X)).map (XT d X).subtype

namespace Geometry
variable {c : PairedMinimality.Configuration d I L X t} (e : Geometry c)
include e

private theorem no_cases : NoCaseInCore c.P c.f ∧ NoCaseInCore c.P c.g := by
  constructor
  · intro A a ha
    rw [e.first_core]
    exact realizes_not_le_blockCore ha
  · intro A a ha
    rw [e.second_core]
    exact realizes_not_le_blockCore ha

/-- B.2 and the core calculation now give both minimal images and all four
concrete possibilities, without extra offender hypotheses. -/
theorem paired_cases (A : Subgroup c.J)
    (hA : A ∈ minimalNontrivialActionFamily c.S c.f) :
    A ∈ minimalNontrivialActionFamily c.S c.g ∧
      ∃ a b : EightCase, a.Realizes (A.map c.f) ∧ b.Realizes (A.map c.g) := by
  obtain ⟨lf, lg, lr⟩ := c.lifting_inputs
  obtain ⟨nf, ng⟩ := e.no_cases
  obtain ⟨hm, a, b, ha, hb, _⟩ := c.paired_minimality_and_cases lf lg lr nf ng A hA
  exact ⟨hm, a, b, ha, hb⟩

private theorem rank_lower (A : Subgroup c.J)
    (hA : A ∈ elementaryAbelianMaxSubgroups c.S) :
    fixedCodim eightRepresentation (A.map c.f) + fixedCodim eightRepresentation (A.map c.g) ≤
      rank (A.map (Configuration.q c e.s_le_t)) +
      rank (A.map c.f ⊓ (Configuration.q c e.s_le_t).ker.map c.f) +
      rank ((A ⊓ (Configuration.q c e.s_le_t).ker).map c.g) := by
  let _ := c.first_normal
  let _ := c.second_normal
  let _ := c.first_elementary
  let _ := c.second_elementary
  rw [c.action.fixedCodim_restrict c.J c.local_le (c.first_le.trans le_sup_right),
    c.conjugateAction.fixedCodim_restrict c.J c.local_le_conjugate
      (c.second_le.trans le_sup_right)]
  exact paired_offender_rank_inequality c.S c.U c.V A
    (fun _ h => c.first_le h) (fun _ h => c.second_le h) c.commutes c.disjoint hA
    _ c.f c.g c.first_kernel c.second_kernel

private theorem quotient_compatible (s : c.S) :
    (Configuration.q c e.s_le_t).subgroupMap c.S (e.actorConj s) =
      e.quotientConj ((Configuration.q c e.s_le_t).subgroupMap c.S s) := by
  apply Subtype.ext
  change quotientMap d X (Configuration.toXT c e.s_le_t (e.actorConj s)) = _
  rw [e.quotientConj_eq]
  have he : Configuration.toXT c e.s_le_t (e.actorConj s) =
      (⟨t, (le_sup_right : (d.T : Subgroup G) ≤ XT d X) c.t_mem⟩ : XT d X) * Configuration.toXT c e.s_le_t s *
        (⟨t, (le_sup_right : (d.T : Subgroup G) ≤ XT d X) c.t_mem⟩ : XT d X)⁻¹ := Subtype.ext (e.actorConj_eq s)
  rw [he, map_mul, map_mul, map_inv]
  rfl

private theorem action_image (A : Subgroup c.J) (hAS : A ≤ c.S)
    (f : c.J →* EightPerm) :
    (A.subgroupOf c.S).map (f.comp c.S.subtype) = A.map f := by
  rw [← map_map, map_subgroupOf_eq_of_le hAS]

/-- The semidihedral alternative contradicts the actual paired rank inequality. -/
theorem conjugator_mem (A : Subgroup c.J)
    (hA : A ∈ minimalNontrivialActionFamily c.S c.f) :
    Configuration.tq c ∈ c.S.map (Configuration.q c e.s_le_t) := by
  by_contra ht
  obtain ⟨_, a, b, ha, hb⟩ := e.paired_cases A hA
  have hne : c.S.map (Configuration.q c e.s_le_t) ≠ Configuration.Timage c := by
    intro he
    exact ht (he ▸ Configuration.tq_mem_Timage c)
  obtain ⟨P, ⟨v⟩⟩ := e.extension hne
  obtain ⟨vSD⟩ := GL2_three_sylow_equiv P
  let j := inclusion (Configuration.Simage_le_Timage c e.s_le_t)
  let τ : Configuration.Timage c := ⟨Configuration.tq c, Configuration.tq_mem_Timage c⟩
  have hj : Function.Injective j := inclusion_injective _
  have hout : τ ∉ j.range := by
    rintro ⟨x, hx⟩
    have hh : (x : XT d X ⧸ pCore 2 (XT d X)) = Configuration.tq c :=
      congrArg Subtype.val hx
    apply ht
    rw [← hh]
    exact x.property
  have hconj : ∀ x, j (e.quotientConj x) = τ * j x * τ⁻¹ := by
    intro x
    exact Subtype.ext (e.quotientConj_eq x)
  have ha' : a.Realizes ((A.subgroupOf c.S).map (c.f.comp c.S.subtype)) :=
    (e.action_image A hA.1.1 c.f).symm ▸ ha
  have hb' : b.Realizes ((A.subgroupOf c.S).map (c.g.comp c.S.subtype)) :=
    (e.action_image A hA.1.1 c.g).symm ▸ hb
  have hp := (localCoordinates e.first).cases_of_semidihedral (localCoordinates e.second)
    ((Configuration.q c e.s_le_t).subgroupMap_surjective c.S)
    e.actorConj e.quotientConj e.quotient_compatible e.relabel e.actionConj
    (v.trans vSD) j hj τ hout hconj ha' hb'
  have hl := e.rank_lower A hA.1
  rw [(EightCase.dimensions ha).2, (EightCase.dimensions hb).2] at hl
  have hf : (Configuration.q c e.s_le_t).ker.map c.f = blockCore :=
    e.core ▸ e.first_core
  have hg : (Configuration.q c e.s_le_t).ker.map c.g = blockCore :=
    e.core ▸ e.second_core
  rcases hp with hp | hp | ⟨rfl, rfl⟩
  · exact (not_lt_of_ge hl) (paired_rank_lt_of_regular_transposition e.first e.second
      hA.1.1 hf hg ha hb (Or.inl hp))
  · exact (not_lt_of_ge hl) (paired_rank_lt_of_regular_transposition e.first e.second
      hA.1.1 hf hg ha hb (Or.inr hp))
  · exact (not_lt_of_ge hl) (paired_rank_lt_of_same_case e.first e.second
      hA.1.1 hf hg ha hb (by decide))

/-- The equal-image branch leaves exactly the four disjoint transpositions
on both modules; all other cases violate the paired rank inequality. -/
theorem disjoint_cases (A : Subgroup c.J)
    (hA : A ∈ minimalNontrivialActionFamily c.S c.f) :
    EightCase.disjoint.Realizes (A.map c.f) ∧ EightCase.disjoint.Realizes (A.map c.g) := by
  obtain ⟨_, a, b, ha, hb⟩ := e.paired_cases A hA
  have ht := e.conjugator_mem A hA
  have ht' : Configuration.tq c ∈ (c.S.map (Configuration.q c e.s_le_t)).subtype.range :=
    ⟨⟨_, ht⟩, rfl⟩
  have he := (localCoordinates e.first).cases_of_inner (localCoordinates e.second)
    ((Configuration.q c e.s_le_t).subgroupMap_surjective c.S)
    e.actorConj e.quotientConj e.quotient_compatible e.relabel e.actionConj
    _ (c.S.map (Configuration.q c e.s_le_t)).subtype_injective
    (Configuration.tq c) ht' e.quotientConj_eq
    ((e.action_image A hA.1.1 c.f).symm ▸ ha)
    ((e.action_image A hA.1.1 c.g).symm ▸ hb)
  subst b
  have hd : a = .disjoint := by
    by_contra hn
    have hl := e.rank_lower A hA.1
    rw [(EightCase.dimensions ha).2, (EightCase.dimensions hb).2] at hl
    exact (not_lt_of_ge hl) (paired_rank_lt_of_same_case e.first e.second hA.1.1
      (e.core ▸ e.first_core) (e.core ▸ e.second_core) ha hb hn)
  subst a
  exact ⟨ha, hb⟩

/-- Equality in the computed bound constructs the source replacement
W C_A(W); it is maximum in S and centralizes the first actual module. -/
theorem replacement (A : Subgroup c.J)
    (hA : A ∈ minimalNontrivialActionFamily c.S c.f) :
    let B := (c.U ⊔ c.V) ⊔ (A ⊓ centralizer ((c.U ⊔ c.V : Subgroup c.J) : Set c.J))
    B ∈ elementaryAbelianMaxSubgroups c.S ∧ B ≤ c.f.ker := by
  obtain ⟨ha, hb⟩ := e.disjoint_cases A hA
  let _ := c.first_normal
  let _ := c.second_normal
  let _ := c.first_elementary
  let _ := c.second_elementary
  have hnum := paired_rank_bound_of_realizes e.first e.second hA.1.1
    (e.core ▸ e.first_core) (e.core ▸ e.second_core) ha hb
  have hfd := c.action.fixedCodim_restrict c.J c.local_le (c.first_le.trans le_sup_right) A
  have hgd := c.conjugateAction.fixedCodim_restrict c.J c.local_le_conjugate
    (c.second_le.trans le_sup_right) A
  have hbound : rank (A.map (Configuration.q c e.s_le_t)) +
      rank (A.map c.f ⊓ (Configuration.q c e.s_le_t).ker.map c.f) +
      rank ((A ⊓ (Configuration.q c e.s_le_t).ker).map c.g) ≤
      (rank c.U - rank (c.U ⊓ centralizer (A : Set c.J))) +
      (rank c.V - rank (c.V ⊓ centralizer (A : Set c.J))) := by
    rw [← hfd, ← hgd, (EightCase.dimensions ha).2, (EightCase.dimensions hb).2]
    exact hnum
  refine ⟨paired_replacement_mem_max c.S c.U c.V A
    (fun _ h => c.first_le h) (fun _ h => c.second_le h) c.commutes c.disjoint hA.1
    _ c.f c.g c.first_kernel c.second_kernel hbound, ?_⟩
  rw [c.first_kernel]
  refine sup_le (sup_le ?_ c.commutes) ?_
  · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  · intro x hx u hu
    exact hx.2 u (mem_sup_left hu)

private theorem mem_S0 (x : c.J) (hx : x ∈ c.S) :
    (x : G) ∈ d.S0 L ↔ c.f x ∈ alternatingGroup (Fin 8) := by
  rw [e.even_preimage]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have he : y = Configuration.toXT c e.s_le_t x := Subtype.ext hyx
    rw [he] at hy
    obtain ⟨z, hz, hez⟩ := hy
    apply ((localCoordinates e.first).mem_marked ⟨x, hx⟩).mp
    have hez' : z = (Configuration.q c e.s_le_t).subgroupMap c.S ⟨x, hx⟩ :=
      Subtype.ext hez
    exact hez' ▸ hz
  · intro hp
    have hm := ((localCoordinates e.first).mem_marked ⟨x, hx⟩).mpr hp
    exact ⟨Configuration.toXT c e.s_le_t x,
      ⟨(Configuration.q c e.s_le_t).subgroupMap c.S ⟨x, hx⟩, hm, rfl⟩, rfl⟩

/-- The minimal action image itself is excluded from the image of the
literal S0 = S ∩ LO2(LS), as needed by the Thompson selection theorem. -/
theorem minimal_image_exclusion (A : Subgroup c.J)
    (hA : A ∈ minimalNontrivialActionFamily c.S c.f) :
    ¬ A.map c.f ≤ ((d.S0 L).subgroupOf c.J).map c.f := by
  intro h
  apply EightCase.disjoint_not_le_alternating (e.disjoint_cases A hA).1
  apply h.trans
  rintro x ⟨a, ha, rfl⟩
  exact (e.mem_S0 a ha.1).mp ha

/-- A single minimal offender excludes the larger quotient. Generation of
T by S and the chosen conjugator then gives equality of the actual images. -/
theorem quotient_images_eq (A : Subgroup c.J)
    (hA : A ∈ minimalNontrivialActionFamily c.S c.f) :
    c.S.map (Configuration.q c e.s_le_t) = Configuration.Timage c := by
  have ht := e.conjugator_mem A hA
  let R := c.S.map (Configuration.q c e.s_le_t)
  have hT : (d.T : Subgroup G) ≤
      (R.comap (quotientMap d X)).map (XT d X).subtype := by
    rw [e.generation]
    refine sup_le ?_ (zpowers_le.mpr ?_)
    · intro x hx
      let y : c.J := ⟨x, (le_sup_right : d.S ≤ c.J) hx⟩
      exact ⟨Configuration.toXT c e.s_le_t y, mem_map_of_mem _ hx, rfl⟩
    · exact ⟨⟨t, (le_sup_right : (d.T : Subgroup G) ≤ XT d X) c.t_mem⟩, ht, rfl⟩
  apply le_antisymm (Configuration.Simage_le_Timage c e.s_le_t)
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨z, hz, he⟩ := hT hy
  have he' : z = y := Subtype.ext he
  exact he' ▸ hz

/-- T normalizes the actual S0 preimage. Normality is relative to T,
not to the ambient group. -/
theorem normalizes_S0 (A : Subgroup c.J)
    (hA : A ∈ minimalNontrivialActionFamily c.S c.f) :
    (d.T : Subgroup G) ≤ normalizer (d.S0 L : Set G) := by
  let R := c.S.map (Configuration.q c e.s_le_t)
  let D := (localCoordinates e.first).marked
  have hn : D.Normal :=
    (inferInstance : evenFour.Normal).map
      (localCoordinates e.first).quotientEquiv.symm.toMonoidHom
      (localCoordinates e.first).quotientEquiv.symm.surjective
  let _ := hn
  have hR : R ≤ normalizer (D.map R.subtype : Set _) := by
    have h := Subgroup.le_normalizer_map (H := D) R.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, R.range_subtype] at h
  have hT : ((d.T : Subgroup G).subgroupOf (XT d X)).map (quotientMap d X) ≤
      normalizer (D.map R.subtype : Set _) := by
    change Configuration.Timage c ≤ _
    rw [← e.quotient_images_eq A hA]
    exact hR
  have hpre := (map_le_iff_le_comap.mp hT).trans
    (Subgroup.le_normalizer_comap (H := D.map R.subtype) (quotientMap d X))
  have hglobal := (map_mono hpre).trans
    (Subgroup.le_normalizer_map (H := (D.map R.subtype).comap (quotientMap d X)) (XT d X).subtype)
  rw [map_subgroupOf_eq_of_le (show (d.T : Subgroup G) ≤ XT d X from le_sup_right)] at hglobal
  rw [e.even_preimage]
  exact hglobal

/-- The first action kernel lies in S0 by its actual parity, with no
Thompson-containment assumption. -/
theorem kernel_le_S0 : c.f.ker ≤ (d.S0 L).subgroupOf c.J := by
  intro x hx
  apply (e.mem_S0 x (c.first_kernel_le hx)).mpr
  change c.f x = 1 at hx
  rw [hx]
  exact one_mem _

end Geometry

namespace Configuration
variable (c : PairedMinimality.Configuration d I L X t)

/-- The actual noncentral component of J(I) and the source Sylow S supply a
minimal nonidentity image for the restricted XS-action. -/
theorem minimal_family_nonempty (R : Sylow 2 I)
    (hR : (R : Subgroup I) = d.S.subgroupOf I)
    (hLJ : L ≤ elementaryAbelianMaxJ I)
    (hnoncentral : ¬ L ≤ centralizer (d.componentModule I L : Set G)) :
    (minimalNontrivialActionFamily c.S c.f).Nonempty := by
  apply minimal_action_family_nonempty
  intro hJ
  let j := inclusion c.local_le
  have hm : c.S.map j = d.S.subgroupOf I := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      change (x : G) ∈ d.S
      have hv : (y : G) = (x : G) := congrArg Subtype.val he
      rw [← hv]
      exact hy
    · intro hx
      exact ⟨⟨x, (le_sup_right : d.S ≤ c.J) hx⟩, hx, Subtype.ext rfl⟩
  have hj : elementaryAbelianMaxJ (d.S.subgroupOf I) ≤ c.action.actor.ker := by
    rw [← hm, elementaryAbelianMaxJ_map_injective j (inclusion_injective c.local_le)]
    rintro x ⟨y, hy, rfl⟩
    exact hJ hy
  obtain ⟨A, hA⟩ := minimal_action_family_nonempty_of_component I L R c.action.actor
    hLJ (fun h => hnoncentral (h.trans c.action.ker_le_centralizer))
  rw [hR] at hA
  exact hA.2.1.1 ((Subgroup.map_eq_bot_iff _).mpr ((le_sSup hA.1).trans hj))

end Configuration

namespace Geometry
variable {c : PairedMinimality.Configuration d I L X t} (e : Geometry c)
include e

/-- Complete offender output under the genuine 15.3.32 geometry. Every B.2
premise and numerical comparison has been discharged. The replacement is a
maximum elementary subgroup lying in the actual centralizer C_I(U_L), and
it gives the terminal Thompson equality. -/
theorem conclusions (R : Sylow 2 I)
    (hR : (R : Subgroup I) = d.S.subgroupOf I)
    (hLJ : L ≤ elementaryAbelianMaxJ I)
    (hnoncentral : ¬ L ≤ centralizer (d.componentModule I L : Set G))
    (hker : c.f.ker.map c.J.subtype = I ⊓ centralizer (d.componentModule I L : Set G)) :
    (minimalNontrivialActionFamily c.S c.f).Nonempty ∧
    (d.T : Subgroup G) ≤ normalizer (d.S0 L : Set G) ∧
    (∀ A ∈ minimalNontrivialActionFamily c.S c.f,
      ¬ A.map c.f ≤ ((d.S0 L).subgroupOf c.J).map c.f) ∧
    (∃ B ∈ elementaryAbelianMaxSubgroups c.S, B ≤ c.f.ker ∧
      B.map c.J.subtype ≤ I ⊓ centralizer (d.componentModule I L : Set G)) ∧
    elementaryAbelianMaxJ (d.S0 L) =
      elementaryAbelianMaxJ (I ⊓ centralizer (d.componentModule I L : Set G)) := by
  have hn := Configuration.minimal_family_nonempty c R hR hLJ hnoncentral
  obtain ⟨A, hA⟩ := hn
  obtain ⟨hB, hBK⟩ := e.replacement A hA
  have hCS0 : I ⊓ centralizer (d.componentModule I L : Set G) ≤ d.S0 L := by
    rw [← hker]
    rintro x ⟨y, hy, rfl⟩
    exact e.kernel_le_S0 hy
  refine ⟨⟨A, hA⟩, e.normalizes_S0 A hA, e.minimal_image_exclusion, ⟨_, hB, hBK, ?_⟩, ?_⟩
  · exact (map_mono hBK).trans_eq hker
  · exact ambient_thompson_eq_of_local_replacement c.J d.S (d.S0 L)
      (I ⊓ centralizer (d.componentModule I L : Set G)) c.f _
      le_sup_right inf_le_left hCS0 hker hB hBK e.minimal_image_exclusion

/-- Consumer of the offender calculation and the preceding source uniqueness
facts: the outside component is impossible. The remaining inputs here are
local geometry and earlier-source hypotheses, never a Thompson conclusion. -/
theorem outside_contradiction (R : Sylow 2 I)
    (hR : (R : Subgroup I) = d.S.subgroupOf I)
    (hLJ : L ≤ elementaryAbelianMaxJ I)
    (hnoncentral : ¬ L ≤ centralizer (d.componentModule I L : Set G))
    (hker : c.f.ker.map c.J.subtype = I ⊓ centralizer (d.componentModule I L : Set G))
    (hYL : d.Yplus ≤ L) (hLM : ¬ L ≤ d.M)
    (hunique : Chapter4.UniqueMaximalOvergroup (d.Yplus ⊔ (d.T : Subgroup G)) d.M) :
    False := by
  obtain ⟨_, hT, _, _, hJ⟩ := e.conclusions R hR hLJ hnoncentral hker
  have hCS0 : I ⊓ centralizer (d.componentModule I L : Set G) ≤ d.S0 L := by
    rw [← hker]
    rintro x ⟨y, hy, rfl⟩
    exact e.kernel_le_S0 hy
  have hJC : elementaryAbelianMaxJ (d.S0 L) ≤
      I ⊓ centralizer (d.componentModule I L : Set G) := by
    rw [hJ]
    exact sSup_le fun _ hA => hA.1
  have hLI : L ≤ I := hLJ.trans (sSup_le fun _ hA => hA.1)
  have hLC : L ≤ normalizer (I ⊓ centralizer (d.componentModule I L : Set G) : Set G) :=
    (le_inf (hLI.trans I.le_normalizer)
      (hLI.trans (c.action.normalizes.trans
        (normalizer_le_normalizer_centralizer _)))).trans inf_normalizer_le_normalizer_inf
  let _ := c.first_elementary
  let E := c.U.map c.J.subtype
  let _ : IsElementaryAbelian 2 E := IsElementaryAbelian.map c.J.subtype
  have hUE : E = d.componentModule I L :=
    map_subgroupOf_eq_of_le (c.first_le.trans le_sup_right)
  have hUK : c.U ≤ c.f.ker := by
    rw [c.first_kernel]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hES0 : E ≤ d.S0 L := by
    rintro x ⟨y, hy, rfl⟩
    exact e.kernel_le_S0 (hUK hy)
  have hE : E ≠ ⊥ := by
    intro he
    have hc := c.action.card_module
    rw [← hUE, he, card_bot] at hc
    norm_num at hc
  exact outside_contradiction_of_thompson_containment d.T (d.S0 L)
    (I ⊓ centralizer (d.componentModule I L : Set G)) E L d.Yplus d.M
    (inf_le_left.trans e.s_le_t) hCS0 hT hLC hJC hES0 hE hYL hLM hunique

end Geometry

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders
