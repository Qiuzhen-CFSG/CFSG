module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.SourceProduct
public import Theory.GroupTheory.NormalSymmetricThreeSupplement
public import Theory.Representation.BinaryPermutation.SixCoreStabilizer

/-!
# The two symmetric-three factors in the ordinary solvable branch

The original five-dimensional marking identifies C_L(z) with a two-group
extension of the actual A₆ vector stabilizer. Its intrinsic two-core quotient
is S₃. This also proves the order and cubic-divisor premises for the literal
L₁=O^{3′}(C_L(z)). Normality of C_L(z) in C_M(z)=L₁T extends its S₃ quotient
across the original Sylow subgroup. The normal Thompson supplement I then
identifies C_G(z)/O₂(C_G(z)) with S₃ × S₃.

The final theorem applies this calculation to SourceProduct's constructed
H=L₁IT. Neither the product, either local quotient, nor the residual order
is an assumption of that endpoint. Its earlier-source premises retain their
final discharge with qt-d-1341-fixed-core-source. Ordinary-row selection,
R₁ placement and normalization, A₆-block noncentrality, the larger-kernel
case, uniqueness of IT, and the marked chamber remain obligations of
qt-d-1341-solvable-source. This is a branch theorem, not full 13.4.8–9.

Source: Aschbacher–Smith, 13.4.8(2–3) and the opening of 13.4.9,
printed pp.905–906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 BinaryNaturalDual.VectorStabilizers Stellmacher
open Chapter14.Section03.FaithfulSource Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The ordinary A6 row identifies the actual action kernel with O₂(L). -/
theorem centralCore_eq_twoCore_of_ordinary
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    centralCore L = pCore 2 L := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he : e x ∈ center (alternatingGroup (Fin 6)) :=
      (Subgroup.centerCongr e ⟨x,hx⟩).property
    rw [Theory.SpecificGroups.SymmetricSix.a6_center_eq_bot,mem_bot] at he
    exact e.map_eq_one_iff.mp he
  change (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) = _
  rw [hz,MonoidHom.comap_bot,QuotientGroup.ker_mk']

/-- In the ordinary row, the original component centralizer has S3 quotient. -/
theorem component_centralizer_quotient (D : ChosenModule T L V) (m : CoreMarking D)
    (hcore : IsPGroup 2 (centralCore L)) (z : V)
    (hz : z.val ∉ centralizer (L : Set G)) :
    let C := L ⊓ centralizer ({z.val} : Set G)
    Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) := by
  let C := L ⊓ centralizer ({z.val} : Set G)
  let w := (m.coordinate z).toAdd
  let S := BinaryPermutation.SixCoreStabilizer.stabilizer w
  let q : L →* alternatingGroup (Fin 6) :=
    m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hq : Function.Surjective q :=
    m.quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have heq (l : L) : q l ∈ S ↔ l.val ∈ centralizer ({z.val} : Set G) := by
    change BinaryPermutation.alternatingCoreRepresentation (Fin 6) (q l) w = w ↔ _
    change BinaryPermutation.coreRepresentation (Fin 6)
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val (m.coordinate z).toAdd =
        (m.coordinate z).toAdd ↔ _
    rw [← m.equivariant l z]
    rw [Multiplicative.toAdd.injective.eq_iff,m.coordinate.injective.eq_iff,Subtype.ext_iff]
    change l.val * z.val * l.val⁻¹ = z.val ↔ _
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  let k : C →* L := inclusion inf_le_left
  let f : C →* S := (q.comp k).codRestrict S (fun c => (heq (k c)).mpr c.property.2)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨l,hl⟩ := hq a.val
    have hlC : l.val ∈ C := ⟨l.property,(heq l).mp (hl ▸ a.property)⟩
    exact ⟨⟨l.val,hlC⟩,Subtype.ext hl⟩
  have hk : f.ker = (centralCore L).comap k := by
    ext c
    change (⟨q (k c),_⟩ : S) = 1 ↔ k c ∈ centralCore L
    rw [Subtype.ext_iff]
    change m.quotient (QuotientGroup.mk' (centralCore L) (k c)) = 1 ↔ _
    rw [m.quotient.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  have hpk : IsPGroup 2 f.ker := by
    rw [hk]
    exact hcore.comap_of_injective k (inclusion_injective _)
  have hfix : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a w = w := by
    intro h
    apply hz
    exact (m.mem_fixed_iff z).mpr
      ((BinaryPermutation.core_fixed_iff_constant (by simp) w).mp h)
  obtain ⟨e⟩ := BinaryPermutation.SixCoreStabilizer.quotient_equiv w hfix
  exact ⟨(f.pCoreQuotientEquiv hf hpk).trans e⟩

/-- The same marking supplies the actual residual's order and cubic divisor. -/
theorem firstCentralizerResidual_order_of_core_marking
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcore : IsPGroup 2 (centralCore L)) (z : V)
    (hz : z.val ∉ centralizer (L : Set G)) :
    (∃ a b : ℕ, Nat.card (firstCentralizerResidual L z.val) ∣ 2 ^ a * 3 ^ b) ∧
      3 ∣ Nat.card (firstCentralizerResidual L z.val) := by
  let C := L ⊓ centralizer ({z.val} : Set G)
  obtain ⟨e⟩ := component_centralizer_quotient D m hcore z hz
  have hquot : Nat.card (C ⧸ pCore 2 C) = 6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
  have hcard : Nat.card C = 2 ^ (n+1) * 3 := by
    have hh := (pCore 2 C).card_mul_index
    change Nat.card (pCore 2 C) * Nat.card (C ⧸ pCore 2 C) = Nat.card C at hh
    rw [hn,hquot] at hh
    rw [← hh,pow_succ]
    ring
  have hA : Nat.card (firstCentralizerResidual L z.val) = Nat.card (primeToResidual 3 C) := by
    rw [firstCentralizerResidual_eq,card_map_of_injective]
    exact C.subtype_injective
  rw [hA]
  refine ⟨⟨n+1,1,?_⟩,?_⟩
  · simpa only [pow_one,← hcard] using (primeToResidual 3 C).card_subgroup_dvd_card
  · have h3 : 3 ∣ Nat.card C := hcard ▸ dvd_mul_left 3 (2 ^ (n+1))
    rw [← (primeToResidual 3 C).card_mul_index] at h3
    exact (Nat.prime_three.dvd_mul.mp h3).resolve_right
      (Nat.prime_three.coprime_iff_not_dvd.mp (primeToResidual_index_coprime 3))

/-- Extend the component centralizer calculation across the original Sylow. -/
theorem normalizer_centralizer_quotient (D : ChosenModule T L V) (m : CoreMarking D)
    (hcore : IsPGroup 2 (centralCore L)) (z : V)
    (hz : z.val ∉ centralizer (L : Set G))
    (hinter : centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) :
    let K := centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)
    Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) := by
  let H := centralizer ({z.val} : Set G)
  let K := H ⊓ normalizer (L : Set G)
  let C := L ⊓ H
  have hCK : C ≤ K := le_inf inf_le_right (inf_le_left.trans L.le_normalizer)
  have hinterK : K = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := hinter
  have hTK : (T : Subgroup G) ≤ K := hinterK.symm ▸ le_sup_right
  have hKC : K ≤ normalizer (C : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans H.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  let N := C.subgroupOf K
  let P := (T : Subgroup G).subgroupOf K
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hCK).mpr hKC
  have hgen : C ⊔ (T : Subgroup G) = K := by
    apply le_antisymm (sup_le hCK hTK)
    rw [hinterK]
    exact sup_le_sup_right (firstCentralizerResidual_le L z.val) _
  have hgeni : N ⊔ P = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hCK,map_subgroupOf_eq_of_le hTK,
      ← MonoidHom.range_eq_map,range_subtype]
    exact hgen
  obtain ⟨eC⟩ := component_centralizer_quotient D m hcore z hz
  let eN := subgroupOfEquivOfLe hCK
  let e : (N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)).trans eC
  exact NormalSymmetricThree.quotient_symmetricThree_of_normal_twoGroup_supplement N P e
    T.isPGroup'.comap_subtype hgeni

/-- The literal Thompson span and component normalizer give the two independent S3 factors. -/
theorem centralizer_pair_quotient_of_source_product
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcore : IsPGroup 2 (centralCore L)) (z : V)
    (hz : z.val ∉ centralizer (L : Set G))
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hquot :
      let I := conjugateSpanBy (Stellmacher.elementaryAbelianMaxJ R) (centralizer ({z.val} : Set G))
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)))
    (hprod :
      let H := centralizer ({z.val} : Set G)
      H = firstCentralizerResidual L z.val ⊔
        conjugateSpanBy (Stellmacher.elementaryAbelianMaxJ R) H ⊔ (T : Subgroup G))
    (hinter : centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G) =
      firstCentralizerResidual L z.val ⊔ (T : Subgroup G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    Nonempty (((centralizer ({z.val} : Set G)) ⧸ pCore 2 (centralizer ({z.val} : Set G))) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let H := centralizer ({z.val} : Set G)
  let K := H ⊓ normalizer (L : Set G)
  let I := conjugateSpanBy (Stellmacher.elementaryAbelianMaxJ R) H
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hzT
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  have hKH : K ≤ H := inf_le_left
  have hinterK : K = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := hinter
  let N := I.subgroupOf H
  let A := K.subgroupOf H
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hIH).mpr
    (le_normalizer_conjugateSpanBy _ _)
  have hTA : (T.subtype hTH : Subgroup H) ≤ A := by
    intro t ht
    change t.val ∈ K
    rw [hinterK]
    exact (show (T : Subgroup G) ≤ firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
      from le_sup_right) ht
  have hA : A ≠ ⊤ := by
    intro he
    apply hout
    intro a ha
    exact (show (⟨a,ha⟩ : H) ∈ A from he ▸ mem_top _).2
  have hgen : N ⊔ A = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hIH,map_subgroupOf_eq_of_le hKH,
      ← MonoidHom.range_eq_map,range_subtype]
    rw [hinterK,← sup_assoc,sup_comm I]
    exact hprod.symm
  obtain ⟨eI⟩ := hquot
  let eN := subgroupOfEquivOfLe hIH
  obtain ⟨eK⟩ := normalizer_centralizer_quotient D m hcore z hz hinter
  let eA := subgroupOfEquivOfLe hKH
  exact NormalSymmetricThree.quotient_pair_of_normal_supplement N A
    ((QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)).trans eI)
    ((QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans eK)
    (T.subtype hTH) hTA hA hgen

theorem centralizer_pair_quotient_of_baumann_bound
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (v : V) (hz : v.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : v.val ∉ centralizer (L : Set G))
    {K : Type*} [Group K] (f : T →* K) (R : Subgroup G)
    (hR : R = ((pCore 2 K).comap f).map (T : Subgroup G).subtype)
    (hQR : (centralizer ({v.val} : Set G)).pCoreIn 2 ≤ R)
    (hsolv : Group.IsSolvable (centralizer ({v.val} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T v.val).subgroupOf
      (centralizer ({v.val} : Set G)) : Set (centralizer ({v.val} : Set G))) =
      pCore 2 (centralizer ({v.val} : Set G)))
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hAN : firstCentralizerResidual L v.val ≤ normalizer (R : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({v.val} : Set G) →
      centralizer ({v.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3)
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({v.val} : Set G)
    let I := conjugateSpanBy (Stellmacher.elementaryAbelianMaxJ R) H
    Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T v.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L v.val ⊔ I ⊔ (T : Subgroup G) := by
  obtain ⟨e⟩ := ordinary
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary e]
    exact pCore_isPGroup
  obtain ⟨horder,hthree⟩ := firstCentralizerResidual_order_of_core_marking D m hcore v hzL
  obtain ⟨_,_,hq,hm,hp,hi,_,_⟩ :=
    centralizer_single_factor_source_product_of_baumann_bound h₀ h structural hz hzL f R hR hQR
      hsolv hkernel hB hout hindex horder hthree hAN h1339 h1342
  have hRT : R ≤ T := by
    rw [hR]
    exact map_subtype_le _
  exact ⟨centralizer_pair_quotient_of_source_product D m hcore v hzL hz R hRT hq hp hi hout,
    hq,hm,hp⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
