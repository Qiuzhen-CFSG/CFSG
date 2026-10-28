module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryCore
public import Theory.GroupTheory.SolvableResidual.TwoKernel
public import Theory.GroupTheory.PResidual.PerfectImage

/-!
# The perfect seven-centralizer action and the retained binary core

In the surviving binary-triality row, let D = C_L(B) and R = O²(D).
The original seven-centralizer covers L/O₂(L). Its two-group kernel and
perfect quotient make R perfect; R is a genuine relative C-component of
D, normalized by C_T(B). Inclusion induces R/O₂(R) ≃ L/O₂(L), and R
generates exactly the same conjugate spans as L on the original omega-span.

For X = CT and U the original omega-span, E = U ∩ O₂(X) contains the
original Sylow omega-center. Therefore its R-span is all of U. In
particular R normalizes E if and only if U is contained in O₂(X). This
retains the kernel rather than treating U as a subgroup of X/O₂(X).

The same R contains a subgroup of order five centralizing B and escaping
X: its quotient is PSL₂(4), whereas the genuine triality quotient of X
and its two-core have orders prime to five. This supplies an actual
actor for the further seven-centralizer analysis. It does not exclude
the remaining binary configuration or construct the exceptional witness.

Source: Aschbacher--Smith 5.1.10--13, printed pp.634--638, and the
seven-centralizer argument of 5.2.2, printed pp.648--649, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

private theorem residual_covers_quotient (L D : Subgroup G) (hDL : D ≤ L)
    [Group.IsPerfect (L ⧸ pCore 2 L)]
    (hs : Function.Surjective ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hDL))) :
    Group.IsPerfect (residual D) ∧
      ∃ hRL : residual D ≤ L,
        Function.Surjective ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hRL)) ∧
        ∃ e : (residual D ⧸ pCore 2 (residual D)) ≃* (L ⧸ pCore 2 L),
          ∀ x : residual D, e (QuotientGroup.mk' (pCore 2 (residual D)) x) =
            QuotientGroup.mk' (pCore 2 L) (inclusion hRL x) := by
  let q := QuotientGroup.mk' (pCore 2 L)
  let f := q.comp (inclusion hDL)
  have hk : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hDL)
  have heq := pResidual_eq_solvableResidual_of_perfect_image f hs hk
  have hp : Group.IsPerfect (pResidual 2 D) := heq ▸ inferInstance
  let := hp
  have hpR : Group.IsPerfect (residual D) := Group.IsPerfect.ofSurjective
    (D.subtype.subgroupMap_surjective (pResidual 2 D))
  have hRL : residual D ≤ L := (map_subtype_le _).trans hDL
  let g := q.comp (inclusion hRL)
  have hg : Function.Surjective g := by
    intro y
    have hy : y ∈ (pResidual 2 D).map f := by
      rw [map_pResidual_of_surjective 2 f hs,pResidual_eq_top_of_isPerfect 2]
      trivial
    obtain ⟨d,hd,he⟩ := hy
    exact ⟨⟨d,mem_map_of_mem D.subtype hd⟩,he⟩
  have hgk : IsPGroup 2 g.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hRL)
  have hgker : g.ker = pCore 2 (residual D) := by
    have hh := g.comap_pCore_of_ker_isPGroup hg hgk
    rwa [pCore_quotient_pCore_eq_bot 2,MonoidHom.comap_bot] at hh
  exact ⟨hpR,hRL,hg,(QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg),fun _ => rfl⟩

/-- The actual perfect two-residual of the seven-centralizer covers the
original left quotient and induces all its conjugate spans on U. -/
theorem original_binary_triality_seven_residual
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let D := L ⊓ centralizer (B : Set G)
    let R := residual D
    R ≤ D ∧ Group.IsPerfect R ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
      (R.subgroupOf D).IsCComponent ∧
      (T : Subgroup G) ⊓ centralizer (B : Set G) ≤ normalizer (R : Set G) ∧
      ∃ hRL : R ≤ L, ∃ e : (R ⧸ pCore 2 R) ≃* (L ⧸ pCore 2 L),
        (∀ x : R, e (QuotientGroup.mk' (pCore 2 R) x) =
          QuotientGroup.mk' (pCore 2 L) (inclusion hRL x)) ∧
        U = conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) R ∧
        (∀ V : Subgroup G, V ≤ U → conjugateSpanBy V L = conjugateSpanBy V R) := by
  obtain ⟨hn,_,_,_,_,hb,_⟩ := original_binary_triality_module_and_hall
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  let D := L ⊓ centralizer (B : Set G)
  have hl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4 := by simpa [hn] using h.linear
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hl
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let : Group.IsPerfect (L ⧸ pCore 2 L) := Group.IsPerfect.ofSurjective
    (f := (e.trans a).symm.toMonoidHom) (e.trans a).symm.surjective
  obtain ⟨hp,hRL,hs,b,hbq⟩ := residual_covers_quotient L D inf_le_left
    (c.seven_centralizer_covers_left h (.inl hn) le_rfl hb)
  have hRD : residual D ≤ D := map_subtype_le _
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let r := (pResidual 2 D).equivMapOfInjective D.subtype D.subtype_injective
  let rq := QuotientGroup.congr _ _ r (pCore_map_iso 2 r)
  let : IsQuasisimple ((pResidual 2 D) ⧸ pCore 2 (pResidual 2 D)) :=
    IsQuasisimple.of_mulEquiv (rq.trans (b.trans (e.trans a))).symm
  have hcomp : ((residual D).subgroupOf D).IsCComponent := by
    change (((pResidual 2 D).map D.subtype).comap D.subtype).IsCComponent
    rw [comap_map_eq_self_of_injective D.subtype_injective]
    exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (Subgroup.Normal.isSubnormal inferInstance) (isPPerfect_pResidual 2)
  have hnR : (T : Subgroup G) ⊓ centralizer (B : Set G) ≤
      normalizer (residual D : Set G) :=
    ((le_inf (inf_le_left.trans h.sylow_normalizes)
      (inf_le_right.trans (centralizer (B : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image D (pResidual 2 D))
  have hspan (V : Subgroup G)
      (hV : V ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) :
      conjugateSpanBy V L = conjugateSpanBy V (residual D) :=
    conjugateSpanBy_eq_of_quotient_surjective V L _ (pCore 2 L) hRL hs
      (h.core_centralizes_omega_span.trans (centralizer_le hV))
  exact ⟨map_subtype_le _,hp,
    (show ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4 from
      ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩).of_mulEquiv b,
    hcomp,hnR,hRL,b,hbq,hspan _ (le_conjugateSpanBy _ _),hspan⟩

/-- The literal kernel contains omega and generates the whole original
module under the perfect seven-centralizer residual. Invariance under this
actual residual is equivalent to containment of the whole module in the core. -/
theorem original_binary_triality_kernel_span
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let R := residual (L ⊓ centralizer (B : Set G))
    let E := U ⊓ X.pCoreIn 2
    omegaOneCenterAmbient (T : Subgroup G) ≤ E ∧
      conjugateSpanBy E R = U ∧
      (R ≤ normalizer (E : Set G) ↔ U ≤ X.pCoreIn 2) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let R := residual (L ⊓ centralizer (B : Set G))
  let E := U ⊓ X.pCoreIn 2
  obtain ⟨hu,_,_,_,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨_,_,_,_,_,hRL,_,_,hzspan,_⟩ := original_binary_triality_seven_residual
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ U := le_conjugateSpanBy _ _
  have hZX : omegaOneCenterAmbient (T : Subgroup G) ≤ X :=
    (hZ.trans hu.reduced_le_sylow).trans le_sup_right
  have hXC : X ≤ omegaCentralizer T := sup_le
    (original_container_centralizes h hH c hKH hK hKT horbit hY hescape C hC hKC hm)
    sylow_le_omegaCentralizer
  have hZQ : omegaOneCenterAmbient (T : Subgroup G) ≤ X.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le (hZ.trans hu.reduced_le_sylow)) hZX
      (hXC.trans (Subgroup.centralizer_le_normalizer _))
  have hZE : omegaOneCenterAmbient (T : Subgroup G) ≤ E := le_inf hZ hZQ
  have hRU : R ≤ normalizer (U : Set G) := hRL.trans (le_normalizer_conjugateSpanBy _ _)
  have hspan : conjugateSpanBy E R = U := le_antisymm
    (conjugateSpanBy_le inf_le_left hRU)
    (hzspan.le.trans (conjugateSpanBy_mono hZE le_rfl))
  refine ⟨hZE,hspan,?_⟩
  constructor
  · intro hn
    exact (hspan ▸ conjugateSpanBy_le le_rfl hn).trans inf_le_right
  · intro hUQ
    have he : E = U := inf_eq_left.mpr hUQ
    change R ≤ normalizer (E : Set G)
    exact he ▸ hRU

private theorem no_five_of_binary_quotient (X : Subgroup G)
    (he : Nonempty ((X ⧸ pCore 2 X) ≃*
      Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one)) : ¬ 5 ∣ Nat.card X := by
  have hc : Nat.card (X ⧸ pCore 2 X) = 211341312 := by
    rw [Nat.card_congr he.some.toEquiv,
      Triality.Standard.ConcreteBruhat.FixedCellCount.card_carrier,
      Triality.Standard.ConcreteBruhat.FixedCellCount.card_borel]
    norm_num [Triality.Standard.binaryParameters_q]
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 X),hc,hk]
  intro hd
  rcases (by decide : Nat.Prime 5).dvd_mul.mp hd with hq | hp
  · norm_num at hq
  · exact (by decide : ¬ 5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hp)

/-- The perfect residual furnishing the full left action has a quintic
subgroup centralizing the original seven and escaping the same CT. -/
theorem original_binary_triality_seven_quintic_escape
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let R := residual (L ⊓ centralizer (B : Set G))
    ∃ F : Subgroup G, F ≤ R ∧ Nat.card F = 5 ∧
      F ≤ centralizer (B : Set G) ∧ ¬ F ≤ X := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let R := residual (L ⊓ centralizer (B : Set G))
  obtain ⟨hRD,_,hr,_⟩ := original_binary_triality_seven_residual
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hr
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  have hc : Nat.card (R ⧸ pCore 2 R) = 60 := by
    rw [Nat.card_congr (e.trans a).toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd : 5 ∣ Nat.card R := (show 5 ∣ Nat.card (R ⧸ pCore 2 R) by rw [hc]; decide).trans
    (card_quotient_dvd_card (pCore 2 R))
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 5 hd
  let F := (zpowers x).map R.subtype
  have hFR : F ≤ R := map_subtype_le _
  have hFc : Nat.card F = 5 := by
    rw [card_map_of_injective R.subtype_injective,Nat.card_zpowers,hx]
  obtain ⟨hX,_⟩ := original_binary_triality_omega_image_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  refine ⟨F,hFR,hFc,hFR.trans (hRD.trans inf_le_right),?_⟩
  intro hFX
  exact no_five_of_binary_quotient X hX (hFc ▸ card_dvd_of_le hFX)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
