module
public import Theory.Mathieu.M24.LocalGeometry.SextetCore
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoCentral
public import Theory.Mathieu.M24.Properties.InvolutionFixedOrders
import all Theory.Mathieu.M24.Block

/-!
# The native second-involution centralizer bound for source 41.2

The fifteen octads fixed by the native 2B representative recover a partition
of the 24 points into six tetrads: two points lie together precisely when
they belong to the same fixed octads. Its whole centralizer preserves this
partition. An explicit word in the certified Mathieu generators carries it
to the standard sextet, so its order divides 138240.

The established exclusion of a subgroup of order nine bounds its odd part.
If its two-part were 1024, a Sylow subgroup containing the central involution
would make that involution two-central. The proved two-central centralizer
order contradicts the sextet divisibility. Thus the full centralizer has
order at most 7680. The source application compares this with the literal
centralizer inside the original plane normalizer, whose order is 7680;
no alignment of an abstract centralizer with a source normalizer is assumed.

Source: Aschbacher, *Sporadic Groups* (1994), 41.2, printed pp.221–222.
The calculation uses the existing 759-octad Witt design and the actual
sextet stabilizer. The internal Block import accesses its checked generator
reindexing certificate. All finite identities are checked by the kernel.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource.NativeSecond
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry Sporadic.Mathieu.M24InvolutionCentralizers

private def fixedIndices : Finset (Fin 759) :=
  {22,87,149,167,170,272,349,360,362,503,532,536,702,705,755}

private theorem index_fixed : ∀ i : Fin 759,
    m24GeneratorABlockIndex i = i ↔ i ∈ fixedIndices := by
  exact m24ForallFin759_of_chunks
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem blockAt_injective : Function.Injective m24BlockAt := by
  intro i j he
  by_contra hn
  have h := m24BlockAt_inter i j hn
  rw [he,Finset.inter_self,m24BlockAt_card] at h
  omega

private theorem fixed_block_iff (i : Fin 759) :
    involution2B.val • m24BlockAt i = m24BlockAt i ↔ i ∈ fixedIndices := by
  have he : involution2B.val • m24BlockAt i = m24BlockAt (m24GeneratorABlockIndex i) :=
    m24_smul_blockAt_of_mask_eq _ _ _ (m24GeneratorA_mask_action i)
  rw [he,blockAt_injective.eq_iff,index_fixed]

private def fixedIndex (j : Fin 15) : Fin 759 :=
  ![22,87,149,167,170,272,349,360,362,503,532,536,702,705,755] j
private theorem fixedIndices_image : fixedIndices = Finset.univ.image fixedIndex := by decide
private def same (a b : Fin 24) : Prop :=
  ∀ j : Fin 15, a ∈ m24BlockAt (fixedIndex j) ↔ b ∈ m24BlockAt (fixedIndex j)
private instance (a b : Fin 24) : Decidable (same a b) :=
  inferInstanceAs (Decidable (∀ j : Fin 15, a ∈ m24BlockAt (fixedIndex j) ↔ b ∈ m24BlockAt (fixedIndex j)))

private theorem same_iff (a b : Fin 24) : same a b ↔
    ∀ O ∈ m24Blocks, involution2B.val • O = O → (a ∈ O ↔ b ∈ O) := by
  constructor
  · intro h O hO hf
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hO
    have hi := (fixed_block_iff i).mp hf
    rw [fixedIndices_image] at hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact h j
  · intro h j
    have hi : fixedIndex j ∈ fixedIndices := by
      rw [fixedIndices_image]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
    exact h _ (Finset.mem_image.mpr ⟨fixedIndex j,Finset.mem_univ _,rfl⟩)
      ((fixed_block_iff _).mpr hi)

private theorem fixed_same_image (family : Finset (Finset (Fin 24)))
    (t g : Equiv.Perm (Fin 24))
    (hg : g⁻¹ • (family : Set (Finset (Fin 24))) = family)
    (hc : Commute t g) (a b : Fin 24)
    (hab : ∀ O ∈ family, t • O = O → (a ∈ O ↔ b ∈ O)) :
    ∀ O ∈ family, t • O = O → (g a ∈ O ↔ g b ∈ O) := by
  intro O hO hf
  have hmem : g⁻¹ • O ∈ family := by
    have hh : g⁻¹ • O ∈ g⁻¹ • (family : Set (Finset (Fin 24))) :=
      Set.smul_mem_smul_set hO
    rwa [hg] at hh
  have hfix : t • (g⁻¹ • O) = g⁻¹ • O := by
    rw [← mul_smul,hc.inv_right.eq,mul_smul,hf]
  have h := hab _ hmem hfix
  simpa only [Finset.mem_inv_smul_finset_iff,Equiv.Perm.smul_def] using h

private theorem same_image (g : centralizer2B) (a b : Fin 24) (hab : same a b) :
    same (g.val.val a) (g.val.val b) := by
  have hg : g.val.val⁻¹ • (m24Blocks : Set (Finset (Fin 24))) = m24Blocks :=
    (mem_M24_iff _).mp (M24.inv_mem g.val.property)
  have hc : Commute involution2B.val g.val.val :=
    (show Commute involution2B g.val from
      (mem_centralizer_singleton_iff.mp g.property).symm).map M24.subtype
  apply (same_iff _ _).mpr
  exact fixed_same_image m24Blocks involution2B.val g.val.val hg hc a b ((same_iff a b).mp hab)

private def part (a : Fin 24) : Finset (Fin 24) := Finset.univ.filter (same a)
private theorem part_image (g : centralizer2B) (a : Fin 24) :
    g.val.val • part a = part (g.val.val a) := by
  ext b
  constructor
  · intro h
    obtain ⟨c,hc,rfl⟩ := Finset.mem_smul_finset.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,same_image g a c (Finset.mem_filter.mp hc).2⟩
  · intro h
    have hh := same_image g⁻¹ (g.val.val a) b (Finset.mem_filter.mp h).2
    have hba : same a (g.val.val.symm b) := by
      change same (g.val.val.symm (g.val.val a)) (g.val.val.symm b) at hh
      simpa only [Equiv.symm_apply_apply] using hh
    exact Finset.mem_smul_finset.mpr ⟨g.val.val.symm b,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hba⟩,g.val.val.apply_symm_apply b⟩


private def label (a : Fin 24) : Fin 6 :=
  ![3,4,0,1,4,0,2,0,1,2,2,3,4,0,5,1,5,1,3,2,3,4,5,5] a
private def tetrad : Fin 6 → Finset (Fin 24)
  | 0 => {2,5,7,13}
  | 1 => {3,8,15,17}
  | 2 => {6,9,10,19}
  | 3 => {0,11,18,20}
  | 4 => {1,4,12,21}
  | 5 => {14,16,22,23}
private theorem part_eq (a : Fin 24) : part a = tetrad (label a) := by
  fin_cases a <;> decide

private def parts : Finset (Finset (Fin 24)) := Finset.univ.image part
private theorem parts_eq : parts = Finset.univ.image tetrad := by
  change Finset.univ.image (fun a => part a) = _
  simp only [part_eq]
  decide
private def word : List (Fin 3) :=
  [0,1,0,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,1,0,1,0,1,0,1,1]
private def transporter : M24 := FusionData.evaluate word
private theorem parts_transported : transporter • parts = standardSextet.parts := by
  rw [parts_eq]
  change (Finset.univ.image tetrad).image (fun A => A.image transporter.val) = _
  rw [show (transporter.val : Fin 24 → Fin 24) = FusionData.wordPoint word from
    funext (FusionData.evaluate_apply word)]
  decide

private theorem centralizer_le_parts_stabilizer :
    centralizer2B ≤ MulAction.stabilizer M24 parts := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro A hA
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
  rw [show g • part a = part (g.val a) from part_image ⟨g,hg⟩ a]
  exact Finset.mem_image.mpr ⟨g.val a,Finset.mem_univ _,rfl⟩

private theorem centralizer_sextet_placement :
    centralizer2B.map (MulAut.conj transporter).toMonoidHom ≤
      sextetStabilizer standardSextet := by
  have h := Subgroup.map_mono (f := (MulAut.conj transporter).toMonoidHom)
    centralizer_le_parts_stabilizer
  rwa [← MulAction.stabilizer_smul_eq_stabilizer_map_conj,parts_transported] at h

private theorem card_dvd_of_conj_le {H : Type*} [Group H] [Finite H]
    (A B : Subgroup H) (g : H)
    (hle : A.map (MulAut.conj g).toMonoidHom ≤ B) : Nat.card A ∣ Nat.card B := by
  have h := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h

/-- The full native second involution centralizer has order dividing the
order of its actual sextet stabilizer. -/
theorem centralizer_card_dvd_sextet : Nat.card centralizer2B ∣ 138240 := by
  rw [← SextetCore.stabilizer_card]
  exact card_dvd_of_conj_le _ _ transporter centralizer_sextet_placement

open Theory.GroupTheory.DoubleCoverCentralizer

private theorem twoCentral_of_full_two_part {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 244823040) (x : G) (hx : orderOf x = 2)
    (h : 1024 ∣ Nat.card (centralizer ({x} : Set G))) : TwoCentral x := by
  let C := centralizer ({x} : Set G)
  let t : C := ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩
  have ht : orderOf t = 2 := (Subgroup.orderOf_coe t).symm.trans hx
  obtain ⟨Q,hQ,hQt⟩ := Sylow.exists_subgroup_card_pow_prime_le 2
    (show 2^10 ∣ Nat.card C from h) (zpowers t)
    (show Nat.card (zpowers t) = 2^1 by rw [Nat.card_zpowers,ht]; rfl) (by omega)
  let P : Subgroup G := Q.map C.subtype
  have hP : Nat.card P = 1024 :=
    (card_map_of_injective C.subtype_injective).trans hQ
  have hind : ¬ 2 ∣ P.index := by
    have hc := P.card_mul_index
    rw [hP,hG] at hc
    have hi : P.index = 239085 := by omega
    rw [hi]
    decide
  let S : Sylow 2 G := (IsPGroup.of_card (p := 2) (n := 10) hP).toSylow hind
  have htS : x ∈ S := mem_map_of_mem _ (hQt (mem_zpowers t))
  have htc : (⟨x,htS⟩ : S) ∈ center S := by
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (map_subtype_le Q a.property)
  exact ⟨S,htS,htc⟩

/-- The native second centralizer does not contain a full ambient Sylow two-subgroup. -/
theorem centralizer_not_1024 :
    ¬ 1024 ∣ Nat.card centralizer2B := by
  intro h
  have hc := card_centralizer_of_twoCentral involution2B involution2B_order
    (twoCentral_of_full_two_part m24_order involution2B involution2B_order h)
  change Nat.card centralizer2B = 21504 at hc
  have hd := centralizer_card_dvd_sextet
  rw [hc] at hd
  norm_num at hd

/-- The precise native upper bound needed for source local placement. -/
theorem centralizer_card_bound :
    Nat.card centralizer2B ≤ 7680 := by
  have h9 := M24InvolutionFixedOrders.centralizer_twoB_not_nine
  have h1024 := centralizer_not_1024
  obtain ⟨k,hk⟩ := centralizer_card_dvd_sextet
  by_contra hn
  have hkb : k ≤ 18 := by nlinarith
  interval_cases k <;> omega

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource.NativeSecond
