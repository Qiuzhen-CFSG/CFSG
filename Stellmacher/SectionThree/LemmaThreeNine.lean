module

public import Stellmacher.SectionThree.LemmaThreeEightCore
public import Stellmacher.SectionThree.ThreeNineCoreQuotient
public import Stellmacher.SectionThree.OmegaNormalClosureElementary
public import Stellmacher.SectionThree.ThreeNineQuotientDichotomy
public import Stellmacher.BaumannNormalizer

/-!
# Stellmacher (3.9)

Let `P₁` and `P₂` be two solvable members of the distinguished local
family with common Sylow subgroup `S`, and put `H = P₁ ⊔ P₂`.
Under the maximal-normal-series and Thompson-subgroup hypotheses supplied by
Stellmacher (3.8), this module proves the three alternatives of Lemma (3.9):
both ordered triple commutators vanish, the Baumann subgroup lies in one
local two-core, or the two first commutators agree.

The proof first disposes of the Baumann alternatives and of the cases where a
local residual centralizes the normal closure
`V = ⟨Ω₁(Z(S))^H⟩`.  Lemma (3.8) and the elementary normal-closure theorem
make `V` elementary abelian.  A maximal normal subgroup containing
`C_H(V)`, together with the quotient-core extension theorem, gives the
core-free faithful quotient required by `threeNine_quotient_dichotomy`.
That theorem supplies exactly the remaining two commutator alternatives.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), Lemma (3.9), pp. 23--24; see
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionThree

universe u

private theorem normalClosure_centralized_by_container_outer
    {G : Type u} [Group G]
    (S H Q : Subgroup G) (hQH : Q ≤ H) (hQS : Q ≤ S)
    (hQnormal : (Q.subgroupOf H).Normal)
    (hOmega : omegaOneCenterAmbient S ≤ Q) :
    let V : Subgroup H := Subgroup.normalClosure
      ((omegaOneCenterAmbient S).subgroupOf H : Set H)
    Q.subgroupOf H ≤ Subgroup.centralizer (V : Set H) := by
  dsimp only
  let V : Subgroup H := Subgroup.normalClosure
    ((omegaOneCenterAmbient S).subgroupOf H : Set H)
  have hVomega : V ≤ omegaOneCenterAmbient (Q.subgroupOf H) :=
    omegaOneCenter_normalClosure_le_containerOmega
      S H Q hQH hQS hQnormal hOmega
  intro q hq
  apply Subgroup.mem_centralizer_iff.mpr
  intro v hv
  have hvomega : v ∈ omegaOneCenterAmbient (Q.subgroupOf H) := hVomega hv
  obtain ⟨_, _, hvcenter⟩ :=
    (mem_omegaOneCenterAmbient_iff (Q.subgroupOf H) v).mp hvomega
  exact (hvcenter q hq).symm

private theorem map_internal_centralizer_le_ambient_outer
    {G : Type u} [Group G] (H V : Subgroup G) (hVH : V ≤ H) :
    (Subgroup.centralizer (V.subgroupOf H : Set H)).map H.subtype ≤
      Subgroup.centralizer (V : Set G) := by
  rintro _ ⟨c, hc, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  let vH : H := ⟨v, hVH hv⟩
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp hc vH
      (Subgroup.mem_subgroupOf.mpr hv))

private theorem triple_commutators_eq_bot_of_residual_centralizes_outer
    {G : Type u} [Group G]
    (H Z V R₁ R₂ : Subgroup G)
    (hVH : V ≤ H) (hVnormal : (V.subgroupOf H).Normal) (hZV : Z ≤ V)
    (hR₂H : R₂ ≤ H)
    (hR₁C : R₁ ≤
      (Subgroup.centralizer (V.subgroupOf H : Set H)).map H.subtype) :
    ⁅⁅Z, R₁⁆, R₂⁆ = ⊥ ∧ ⁅⁅Z, R₂⁆, R₁⁆ = ⊥ := by
  have hR₁CV : R₁ ≤ Subgroup.centralizer (V : Set G) :=
    hR₁C.trans (map_internal_centralizer_le_ambient_outer H V hVH)
  have hVR₁ : ⁅V, R₁⁆ = ⊥ := by
    rw [Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hR₁CV
  have hZR₁ : ⁅Z, R₁⁆ = ⊥ := le_bot_iff.mp
    ((Subgroup.commutator_mono hZV le_rfl).trans hVR₁.le)
  have hR₂normV : R₂ ≤ Subgroup.normalizer (V : Set G) := by
    refine hR₂H.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hVH).mp ?_)
    simpa [subgroupOf_map_subtype_eq] using hVnormal
  have hZR₂V : ⁅Z, R₂⁆ ≤ V :=
    (Subgroup.commutator_mono hZV le_rfl).trans
      ((Subgroup.le_normalizer_iff_commutator_le_left).mp hR₂normV)
  constructor
  · simp [hZR₁]
  · exact le_bot_iff.mp
      ((Subgroup.commutator_mono hZR₂V le_rfl).trans hVR₁.le)

private theorem exists_maximal_normal_containing_centralizer_outer
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (V : Subgroup H) (hVnormal : V.Normal)
    (R₁ R₂ : Subgroup G)
    (hR₁not : ¬ R₁ ≤ (Subgroup.centralizer (V : Set H)).map H.subtype)
    (hR₂not : ¬ R₂ ≤ (Subgroup.centralizer (V : Set H)).map H.subtype) :
    ∃ N : Subgroup G,
      (Subgroup.centralizer (V : Set H)).map H.subtype ≤ N ∧
      N ≤ H ∧ (N.subgroupOf H).Normal ∧
      ¬ R₁ ≤ N ∧ ¬ R₂ ≤ N ∧
      ∀ N' : Subgroup G, N ≤ N' → N' ≤ H →
        (N'.subgroupOf H).Normal →
        (¬ R₁ ≤ N' ∧ ¬ R₂ ≤ N') → N' = N := by
  classical
  let C : Subgroup H := Subgroup.centralizer (V : Set H)
  let Camb : Subgroup G := C.map H.subtype
  let X : Set (Subgroup G) :=
    {K | Camb ≤ K ∧ K ≤ H ∧ (K.subgroupOf H).Normal ∧
      ¬ R₁ ≤ K ∧ ¬ R₂ ≤ K}
  have hCambH : Camb ≤ H := Subgroup.map_subtype_le _
  have hCambNormal : (Camb.subgroupOf H).Normal := by
    let _ : V.Normal := hVnormal
    simpa [Camb, C, subgroupOf_map_subtype_eq] using
      (Subgroup.normal_centralizer : C.Normal)
  have hCambX : Camb ∈ X :=
    ⟨le_rfl, hCambH, hCambNormal, by simpa [Camb, C] using hR₁not,
      by simpa [Camb, C] using hR₂not⟩
  obtain ⟨N, hNmax⟩ := X.toFinite.exists_maximal ⟨Camb, hCambX⟩
  refine ⟨N, hNmax.prop.1, hNmax.prop.2.1, hNmax.prop.2.2.1,
    hNmax.prop.2.2.2.1, hNmax.prop.2.2.2.2, ?_⟩
  intro N' hNN' hN'H hN'normal havoid
  exact (hNmax.eq_of_le ⟨hNmax.prop.1.trans hNN', hN'H, hN'normal,
    havoid.1, havoid.2⟩ hNN').symm

/-- Stellmacher's three-way local commutator dichotomy, Lemma (3.9). -/
public theorem lemma_three_nine
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P₁ P₂ H N : Subgroup G)
    (hP₁ : P₁ ∈ PSet (⊤ : Subgroup G) S)
    (hP₂ : P₂ ∈ PSet (⊤ : Subgroup G) S)
    (hH : H = P₁ ⊔ P₂)
    (hN : N ≤ H ∧ (N.subgroupOf H).Normal ∧
      ¬ twoResidualAmbient P₁ ≤ N ∧
      ¬ twoResidualAmbient P₂ ≤ N ∧
      ∀ N' : Subgroup G, N ≤ N' → N' ≤ H →
        (N'.subgroupOf H).Normal →
        (¬ twoResidualAmbient P₁ ≤ N' ∧
          ¬ twoResidualAmbient P₂ ≤ N') → N' = N)
    (hsolv₁ : Group.IsSolvable P₁)
    (hsolv₂ : Group.IsSolvable P₂)
    (T : Sylow 2 H) (hST : S ≤ sylowAmbient T)
    (Q : Subgroup G) (hQ : Q = S ⊓ twoCoreAmbient H)
    (hsolv : Group.IsSolvable H)
    (hOmega : omegaOneCenterAmbient S ≤ Q)
    (hJ : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (sylowAmbient T)) :
    (⁅⁅omegaOneCenterAmbient S, twoResidualAmbient P₁⁆,
          twoResidualAmbient P₂⁆ = ⊥ ∧
      ⁅⁅omegaOneCenterAmbient S, twoResidualAmbient P₂⁆,
          twoResidualAmbient P₁⁆ = ⊥) ∨
    (S ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) ≤
        twoCoreAmbient P₁ ∨
      S ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) ≤
        twoCoreAmbient P₂) ∨
    ⁅omegaOneCenterAmbient S, twoResidualAmbient P₁⁆ =
      ⁅omegaOneCenterAmbient S, twoResidualAmbient P₂⁆ := by
  classical
  subst Q
  let B : Subgroup G := S ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G)
  by_cases hB₁ : B ≤ twoCoreAmbient P₁
  · exact Or.inr (Or.inl (Or.inl hB₁))
  by_cases hB₂ : B ≤ twoCoreAmbient P₂
  · exact Or.inr (Or.inl (Or.inr hB₂))
  have hSP₁ : S ≤ P₁ := by
    obtain ⟨U, hU⟩ := hP₁.1.2.1
    rw [← hU]
    exact Subgroup.map_subtype_le _
  have hSP₂ : S ≤ P₂ := by
    obtain ⟨U, hU⟩ := hP₂.1.2.1
    rw [← hU]
    exact Subgroup.map_subtype_le _
  have hP₁H : P₁ ≤ H := by rw [hH]; exact le_sup_left
  have hP₂H : P₂ ≤ H := by rw [hH]; exact le_sup_right
  have hSH : S ≤ H := hSP₁.trans hP₁H
  have hQH : S ⊓ twoCoreAmbient H ≤ H :=
    inf_le_right.trans (Subgroup.map_subtype_le _)
  obtain ⟨H₀, H₁, h38⟩ := lemma_three_eight_core_eq_twoCore
    S h P₁ P₂ H N hP₁ hP₂ hH hN hsolv₁ hsolv₂
  let V : Subgroup H := Subgroup.normalClosure
    ((omegaOneCenterAmbient S).subgroupOf H : Set H)
  have hVnormal : V.Normal := Subgroup.normalClosure_normal
  have hVelem : IsElementaryAbelian 2 V :=
    omegaOneCenter_normalClosure_isElementaryAbelian S H
      (S ⊓ twoCoreAmbient H) hQH inf_le_left h38.part_a.2.1 hOmega
  let C : Subgroup H := Subgroup.centralizer (V : Set H)
  have hCnormal : C.Normal := by
    let _ : V.Normal := hVnormal
    exact Subgroup.normal_centralizer
  let Camb : Subgroup G := C.map H.subtype
  let Vamb : Subgroup G := V.map H.subtype
  have hVambH : Vamb ≤ H := Subgroup.map_subtype_le _
  have hVambNormal : (Vamb.subgroupOf H).Normal := by
    simpa [Vamb, subgroupOf_map_subtype_eq] using hVnormal
  have hZVamb : omegaOneCenterAmbient S ≤ Vamb := by
    intro z hz
    have hzS : (z : G) ∈ S :=
      ((mem_omegaOneCenterAmbient_iff S z).mp hz).1
    have hzH : (z : G) ∈ H := hSH hzS
    exact ⟨⟨z, hzH⟩,
      Subgroup.le_normalClosure (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  by_cases hR₁C : twoResidualAmbient P₁ ≤ Camb
  · exact Or.inl (triple_commutators_eq_bot_of_residual_centralizes_outer
      H (omegaOneCenterAmbient S) Vamb (twoResidualAmbient P₁)
        (twoResidualAmbient P₂) hVambH hVambNormal hZVamb
        ((Subgroup.map_subtype_le _).trans hP₂H) (by simpa [Camb, C, Vamb,
          subgroupOf_map_subtype_eq] using hR₁C))
  by_cases hR₂C : twoResidualAmbient P₂ ≤ Camb
  · have ha := triple_commutators_eq_bot_of_residual_centralizes_outer
      H (omegaOneCenterAmbient S) Vamb (twoResidualAmbient P₂)
        (twoResidualAmbient P₁) hVambH hVambNormal hZVamb
        ((Subgroup.map_subtype_le _).trans hP₁H) (by simpa [Camb, C, Vamb,
          subgroupOf_map_subtype_eq] using hR₂C)
    exact Or.inl ⟨ha.2, ha.1⟩
  obtain ⟨N', hCN', hN'H, hN'normal, hR₁N', hR₂N', hN'max⟩ :=
    exists_maximal_normal_containing_centralizer_outer H V hVnormal
      (twoResidualAmbient P₁) (twoResidualAmbient P₂)
      (by simpa [Camb, C] using hR₁C) (by simpa [Camb, C] using hR₂C)
  let hN' : N' ≤ H ∧ (N'.subgroupOf H).Normal ∧
      ¬ twoResidualAmbient P₁ ≤ N' ∧
      ¬ twoResidualAmbient P₂ ≤ N' ∧
      ∀ M : Subgroup G, N' ≤ M → M ≤ H →
        (M.subgroupOf H).Normal →
        (¬ twoResidualAmbient P₁ ≤ M ∧
          ¬ twoResidualAmbient P₂ ≤ M) → M = N' :=
    ⟨hN'H, hN'normal, hR₁N', hR₂N', hN'max⟩
  obtain ⟨H₀', H₁', h38'⟩ := lemma_three_eight_core_eq_twoCore
    S h P₁ P₂ H N' hP₁ hP₂ hH hN' hsolv₁ hsolv₂
  have hQC : (S ⊓ twoCoreAmbient H).subgroupOf H ≤ C := by
    simpa [C, V] using normalClosure_centralized_by_container_outer
      S H (S ⊓ twoCoreAmbient H) hQH inf_le_left h38.part_a.2.1 hOmega
  have hQCanb : S ⊓ twoCoreAmbient H ≤ Camb := by
    intro q hq
    exact ⟨⟨q, hQH hq⟩, hQC (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  have hSN'C : S ⊓ N' ≤ Camb := by
    rw [← h38'.part_a.1]
    exact hQCanb
  have hbarCore' := threeNine_barred_sylow_inf_twoCore_eq_bot
    S H N' P₁ P₂ C hSH hN'H hCN' hCnormal hN'normal
      hR₁N' hR₂N' hN'max hSN'C
  have hbarCore :
      let _ : C.Normal := hCnormal
      let q : H →* H ⧸ C := QuotientGroup.mk' C
      (S.subgroupOf H).map q ⊓ pCore 2 (H ⧸ C) = ⊥ := by
    exact hbarCore'
  rcases threeNine_quotient_dichotomy S h P₁ P₂ H hP₁ hP₂ hH
      hsolv₁ hsolv₂ T hST hsolv hJ V C rfl hVnormal hVelem rfl hCnormal
      (by simpa [Camb] using hR₁C) (by simpa [Camb] using hR₂C)
      (by simpa [B] using hB₁) (by simpa [B] using hB₂) hbarCore with ha | hc
  · exact Or.inl ha
  · exact Or.inr (Or.inr hc)

end Stellmacher.SectionThree
