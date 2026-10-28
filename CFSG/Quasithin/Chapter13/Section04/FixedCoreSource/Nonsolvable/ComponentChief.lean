module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.OrdinaryRow
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.BlockContainment
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex
public import Theory.SpecificGroups.SymmetricFour.ResidualFactorization
public import Theory.Representation.PSL3Two.DoubledCubic

/-!
# The five-dimensional chief budget against a doubled component

Retain the original augmentation core V, its constant line, and an escaping
vector z. Any cubic fixing z fixes a subgroup of V of order at least four,
so its cubic length on V is at most one. If L is a short block, the actual
commutator containment [O₂(LT),L] ≤ V transfers this bound to O₂(LT).
The literal residual L₁=O^{3′}(C_L(z)) has an A₄ quotient with two-kernel;
chief-series comparison therefore bounds every complete noncentral binary
chief count of L₁ by two.

The final theorem applies this budget to a doubled natural SL₃(2) component.
A cubic of L₁ embeds in K/O₂(K), and its length on the two marked summands
is two. The moved subgroup [U,A] lies in the kernel of the actual K-side
A₄ quotient of L₁ and retains that length, contradicting the one-factor
kernel budget. Both quotient kernels and all subgroup inclusions are literal.

This discharges the chief-factor comparison in the doubled row, conditional
on the source short-block conclusion, L₁ ≤ K, normalization by U, and its
K-side A₄ map. Constructing these inputs from the original Baumann and
reciprocal-centralizer arguments remains with qt-d-1341-nonsolvable-source,
as do the other row exclusions and comparison/commutator/graph assembly.
No four-dimensional NaturalSetup or additional ambient exclusion is used.
Universal nonsolvability at both escaping weights remains required by final
assembly, whose earlier-source premises retain their existing producers.

Source: Aschbacher–Smith, 13.4.10(2–4), printed pp.907–909;
13.2.2(7) is the still-required upstream short-block alternative.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A cubic fixing a nonconstant vector in the original five-space has
cubic fixed length at most one. The fixed constant line is retained. -/
theorem core_cubic_length_le_one
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∉ centralizer (L : Set G))
    (A : Subgroup G) (hAL : A ≤ L)
    (hAz : A ≤ centralizer ({z.val} : Set G)) :
    conjugationCubicLength A V ≤ 1 := by
  let C := (centralizer (A : Set G)).subgroupOf V
  let F := (V ⊓ centralizer (L : Set G) : Subgroup G)
  have hFV : F ≤ V := inf_le_left
  have hFC : F.subgroupOf V ≤ C := fun _ hx =>
    (centralizer_le hAL) hx.2
  have hFcard : Nat.card (F.subgroupOf V) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFV).toEquiv).trans m.card_fixed
  have hzC : z ∈ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hAz ha)
  have hproper : ¬ C ≤ F.subgroupOf V := fun hh => hz (hh hzC).2
  have hindex : (F.subgroupOf V).relIndex C ≠ 1 :=
    fun he => hproper (relIndex_eq_one.mp he)
  have hm := ((F.subgroupOf V).subgroupOf C).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hFC).toEquiv,hFcard] at hm
  change 2 * (F.subgroupOf V).relIndex C = Nat.card C at hm
  have hi : 0 < (F.subgroupOf V).relIndex C :=
    Nat.pos_of_ne_zero (by
      intro he
      rw [he] at hm
      have := Nat.card_pos (α := C)
      omega)
  have hc : 4 ≤ Nat.card C := by omega
  have hmul := C.card_mul_index
  rw [m.card_module] at hmul
  have hb : (centralizer (A : Set G)).relIndex V ≤ 8 := by
    change C.index ≤ 8
    nlinarith
  exact (Nat.log_mono_right (b := 4) hb).trans_eq (by decide)

/-- A short original L transfers this fixed length to the entire two-core of LT. -/
theorem core_block_cubic_length_le_one
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∉ centralizer (L : Set G))
    (A : Subgroup G) (hA : Nat.card A = 3) (hAL : A ≤ L)
    (hAz : A ≤ centralizer ({z.val} : Set G)) :
    conjugationCubicLength A ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 1 := by
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  have hQN : Q ≤ normalizer (V : Set G) :=
    D.core_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  let : (V.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer hQN
  have hAQ : A ≤ normalizer (Q : Set G) :=
    (hAL.trans le_sup_left).trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hQT : Q ≤ T := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)] using
      pCoreIn_le_sylow X (T.subtype le_sup_right)
  have hcomm : ⁅Q,A⁆ ≤ V := (commutator_mono
    (le_inf hQT D.core_centralizes) hAL).trans
      (Solvable.sylow_module_centralizer_commutator_le_chosen D hb)
  have he := CubicComparison.length_eq_of_commutator_le A Q V
    (IsPGroup.of_card (n := 1) (by simpa using hA)) (isPGroup_pCoreIn 2 X)
    D.le_core hAQ (hAL.trans D.normalizes) hcomm
  rw [←he]
  exact core_cubic_length_le_one D m z hz A hAL hAz

private theorem symmetricFour_primeToResidual :
    primeToResidual 3 (Equiv.Perm (Fin 4)) = alternatingGroup (Fin 4) := by
  rw [←twoResidual_eq_primeToResidual_three,Theory.SpecificGroups.SymmetricFourResidual.residual_eq]
  rw [IsPiGroup_iff]
  intro p hp
  rw [Nat.card_perm,Nat.card_fin] at hp
  have h : p.val ∣ 2 ^ 3 * 3 := hp
  change p.val = 2 ∨ p.val = 3
  rcases p.property.dvd_mul.mp h with h2 | h3
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)

/-- The literal original cubic residual maps onto A₄, with exactly the
restriction of the original component two-core as kernel. -/
theorem core_firstResidual_alternatingFour
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∉ centralizer (L : Set G)) :
    ∃ f : Solvable.firstCentralizerResidual L z.val →* alternatingGroup (Fin 4),
      Function.Surjective f ∧ f.ker = (L.pCoreIn 2).subgroupOf
        (Solvable.firstCentralizerResidual L z.val) := by
  let C := L ⊓ centralizer ({z.val} : Set G)
  let R := primeToResidual 3 C
  let J := Solvable.firstCentralizerResidual L z.val
  have hJC : J ≤ C := Solvable.firstCentralizerResidual_le L z.val
  have hJ : J = R.map C.subtype := Solvable.firstCentralizerResidual_eq L z.val
  obtain ⟨p,hp,hpk,_⟩ := Solvable.component_centralizer_action D m z
  have hw : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (m.coordinate z).toAdd =
        (m.coordinate z).toAdd := by
    intro hw
    exact hz ((m.mem_fixed_iff z).mpr
      ((BinaryPermutation.core_fixed_iff_constant (by simp) _).mp hw))
  obtain ⟨e⟩ := BinaryPermutation.SixCoreResidualMovement.stabilizer_equiv _ hw
  let q := e.toMonoidHom.comp p
  have hq : Function.Surjective q := e.surjective.comp hp
  have hqk : q.ker = (pCore 2 L).comap (inclusion inf_le_left) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,hpk,
      Solvable.centralCore_eq_twoCore_of_ordinary eL]
  have hr : R.map q = alternatingGroup (Fin 4) :=
    (map_primeToResidual_of_surjective 3 q hq).trans symmetricFour_primeToResidual
  let f : J →* alternatingGroup (Fin 4) :=
    (q.comp (inclusion hJC)).codRestrict _ (fun j => by
      rw [←hr]
      have hj := hJ.le j.property
      obtain ⟨c,hc,he⟩ := hj
      have he' : c = inclusion hJC j := Subtype.ext he
      exact mem_map_of_mem q (he' ▸ hc))
  refine ⟨f,?_,?_⟩
  · intro a
    have ha : a.val ∈ R.map q := hr.symm ▸ a.property
    obtain ⟨c,hc,hca⟩ := ha
    refine ⟨⟨c.val,hJ.ge (mem_map_of_mem C.subtype hc)⟩,?_⟩
    exact Subtype.ext hca
  · ext j
    change f j = 1 ↔ j.val ∈ L.pCoreIn 2
    have hmem : j.val ∈ L.pCoreIn 2 ↔
        (inclusion inf_le_left (inclusion hJC j)) ∈ pCore 2 L :=
      by
        change (inclusion inf_le_left (inclusion hJC j)).val ∈
          (pCore 2 L).map L.subtype ↔ _
        constructor
        · rintro ⟨a,ha,hea⟩
          exact (Subtype.ext hea : a = inclusion inf_le_left (inclusion hJC j)) ▸ ha
        · intro hx
          exact mem_map_of_mem L.subtype hx
    rw [hmem,Subtype.ext_iff]
    change inclusion hJC j ∈ q.ker ↔ _
    rw [hqk]
    rfl

/-- The original five-dimensional short-block branch has at most two
noncentral binary factors in every complete chief series of its actual L₁. -/
theorem core_firstResidual_chief_count_le_two
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∉ centralizer (L : Set G))
    (s : ChiefSeries (Solvable.firstCentralizerResidual L z.val))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : s.noncentralTwoCount ≤ 2 := by
  let J := Solvable.firstCentralizerResidual L z.val
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨f,hf,hker⟩ := core_firstResidual_alternatingFour D m eL z hz
  have hd : 3 ∣ Nat.card J := by
    apply dvd_trans (b := Nat.card (alternatingGroup (Fin 4)))
    · rw [nat_card_alternatingGroup]; norm_num
    · exact card_dvd_of_surjective f hf
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 hd
  let A := zpowers (x : G)
  have hA : Nat.card A = 3 := by rw [Nat.card_zpowers,J.orderOf_coe x,hx]
  have hAJ : A ≤ J := zpowers_le.mpr x.property
  have hAL : A ≤ L := hAJ.trans ((Solvable.firstCentralizerResidual_le L z.val).trans inf_le_left)
  have hAz : A ≤ centralizer ({z.val} : Set G) :=
    hAJ.trans ((Solvable.firstCentralizerResidual_le L z.val).trans inf_le_right)
  have hp : IsPGroup 2 f.ker := by rw [hker]; exact (isPGroup_pCoreIn 2 L).comap_subtype
  have hAi : Nat.card (A.subgroupOf J) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hA
  have hc := CubicComparison.alternatingFour_count f hf hp (A.subgroupOf J) hAi s h0 h1
  have hl : conjugationCubicLength (A.subgroupOf J) f.ker ≤ 1 := by
    rw [hker]
    have he := CubicComparison.length_subgroupOf A (L.pCoreIn 2 ⊓ J) J hAJ inf_le_right
    rw [inf_subgroupOf_right] at he
    rw [he]
    have hLQ : L.pCoreIn 2 ≤ Q := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans le_sup_left)
      ((sup_le L.le_normalizer D.sylow_normalizes_component).trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
    exact (conjugationCubicLength_mono A (inf_le_left.trans hLQ)).trans
      (core_block_cubic_length_le_one D m hb z hz A hA hAL hAz)
  omega

/-- Every other actual A₄ quotient of the same residual has the same
one-factor kernel budget. This is the comparison used on the K side. -/
theorem core_firstResidual_cubic_kernel_le_one
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∉ centralizer (L : Set G))
    (f : Solvable.firstCentralizerResidual L z.val →* alternatingGroup (Fin 4))
    (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (A : Subgroup G) (hA : Nat.card A = 3)
    (hAJ : A ≤ Solvable.firstCentralizerResidual L z.val) :
    conjugationCubicLength A
      (f.ker.map (Solvable.firstCentralizerResidual L z.val).subtype) ≤ 1 := by
  let J := Solvable.firstCentralizerResidual L z.val
  obtain ⟨s,h0,h1⟩ := exists_chiefSeries (⊥ : NormalNode J) ⊤ bot_le
  have hc := core_firstResidual_chief_count_le_two D m hb eL z hz s h0 h1
  have hAi : Nat.card (A.subgroupOf J) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hA
  have he := CubicComparison.alternatingFour_count f hf hp (A.subgroupOf J) hAi s h0 h1
  have hm := CubicComparison.length_subgroupOf A (f.ker.map J.subtype) J hAJ
    (map_subtype_le _)
  have hfm : (f.ker.map J.subtype).subgroupOf J = f.ker := by
    ext x
    change x.val ∈ f.ker.map J.subtype ↔ x ∈ f.ker
    exact mem_map_iff_mem J.subtype_injective
  rw [hfm] at hm
  change conjugationCubicLength A (f.ker.map J.subtype) ≤ 1
  omega


/-- The original short-block chief budget excludes the doubled component
as soon as the source residual has its actual K-side A₄ quotient. All cubic
movement, kernel comparison and full-module transport are proved here. -/
theorem core_block_excludes_doubled_component
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∉ centralizer (L : Set G))
    (K U : Subgroup G)
    (hJK : Solvable.firstCentralizerResidual L z.val ≤ K)
    (hKU : K ≤ normalizer (U : Set G))
    (hUcore : U ≤ K.pCoreIn 2)
    (hUJ : U ≤ normalizer (Solvable.firstCentralizerResidual L z.val : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : U ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : letI := conjMulDistribMulActionOfLeNormalizer K U hKU
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd)
    (f : Solvable.firstCentralizerResidual L z.val →* alternatingGroup (Fin 4))
    (hf : Function.Surjective f)
    (hfk : f.ker = (K.pCoreIn 2).subgroupOf (Solvable.firstCentralizerResidual L z.val)) :
    False := by
  let J := Solvable.firstCentralizerResidual L z.val
  obtain ⟨fL,hfL,_⟩ := core_firstResidual_alternatingFour D m eL z hz
  have hd : 3 ∣ Nat.card J := by
    apply dvd_trans (b := Nat.card (alternatingGroup (Fin 4)))
    · rw [nat_card_alternatingGroup]; norm_num
    · exact card_dvd_of_surjective fL hfL
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 hd
  let A := zpowers (a : G)
  have hA : Nat.card A = 3 := by rw [Nat.card_zpowers,J.orderOf_coe a,ha]
  have hAJ : A ≤ J := zpowers_le.mpr a.property
  have hAK : A ≤ K := hAJ.trans hJK
  have hAU : A ≤ normalizer (U : Set G) := hAK.trans hKU
  let q : A →* BinaryLinearThree.Group :=
    eK.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hAK))
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_of_card_eq
    have hp2 : IsPGroup 2 q.ker := by
      have hk : q.ker = (pCore 2 K).comap (inclusion hAK) := by
        ext x
        change eK (QuotientGroup.mk' (pCore 2 K) (inclusion hAK x)) = 1 ↔ _
        rw [eK.map_eq_one_iff]
        exact QuotientGroup.eq_one_iff _
      rw [hk]
      exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
    have hp3 : IsPGroup 3 q.ker :=
      (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hA)).to_subgroup q.ker
    have hc := (IsPGroup.coprime_card_of_ne 2 3 (by decide)
      q.ker q.ker hp2 hp3).gcd_eq_one
    simpa only [Nat.gcd_self] using hc
  have hlength : conjugationCubicLength A U = 2 :=
    BinaryLinearThree.doubled_natural_cubic_length A U hA hAU q hq e (fun a v => he (inclusion hAK a) v)
  let P := ⁅U,A⁆
  have hPU : P ≤ U := le_normalizer_iff_commutator_le_left.mp hAU
  have hPJ : P ≤ J := (commutator_mono le_rfl hAJ).trans
    (le_normalizer_iff_commutator_le_right.mp hUJ)
  have hPN : P ≤ f.ker.map J.subtype := by
    intro p hp
    exact ⟨⟨p,hPJ hp⟩,hfk.symm ▸ (hPU.trans hUcore) hp,rfl⟩
  let : (P.subgroupOf U).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left U A)
  have hlenP := CubicComparison.length_eq_of_commutator_le A U P
    (IsPGroup.of_card (n := 1) (by simpa using hA))
    ((isPGroup_pCoreIn 2 K).to_le hUcore) hPU hAU
    (normalizer_commutator_ge_right U A) le_rfl
  have hp : IsPGroup 2 f.ker := by rw [hfk]; exact (isPGroup_pCoreIn 2 K).comap_subtype
  have hsmall := core_firstResidual_cubic_kernel_le_one D m hb eL z hz f hf hp A hA hAJ
  change conjugationCubicLength A (f.ker.map J.subtype) ≤ 1 at hsmall
  have hlarge := conjugationCubicLength_mono A hPN
  rw [hlenP,hlength] at hlarge
  omega

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
