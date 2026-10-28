module
public import Theory.SpecificGroups.SymmetricFive.LocalTwoCore
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# Local two-cores in S5 times S3

A subgroup whose order is divisible by nine contains the normal cubic
factor: disjointness would make nine divide its index 240. Its first
projection has order divisible by three. If it also contains an ambient
Sylow two-subgroup, its second projection is the full S3. The existing
S5 two-core theorem and the trivial two-core of S3 then put its entire
two-core in A5 times the identity.

The Section12.6 consumer applies this to the literal image of L1T,
using its original Sylow and the E9 image of the point residual.
Source: Aschbacher--Smith12.6.31(3) and12.6.34, printed pp.835,838.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricFiveThreeLocal
abbrev S5 := Equiv.Perm (Fin 5)
abbrev S3 := Equiv.Perm (Fin 3)
abbrev Product := S5 × S3
@[expose] def cubic : Subgroup Product := (⊥ : Subgroup S5).prod (alternatingGroup (Fin 3))
instance : cubic.Normal := by unfold cubic; infer_instance

theorem cubic_card : Nat.card cubic = 3 := by
  rw [cubic,Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,card_bot,one_mul]
  rw [Nat.card_eq_fintype_card]
  decide

theorem product_card : Nat.card Product = 720 := by
  rw [Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

/-- Every local subgroup with a full nine-part contains the normal cubic factor. -/
theorem cubic_le_of_nine_dvd (J : Subgroup Product) (h9 : 9 ∣ Nat.card J) : cubic ≤ J := by
  have hd : Nat.card (cubic ⊓ J : Subgroup Product) ∣ 3 := by
    simpa only [cubic_card] using card_dvd_of_le (show cubic ⊓ J ≤ cubic from inf_le_left)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h1 | h3
  · have hi : cubic ⊓ J = ⊥ := (eq_bot_iff_card _).mpr h1
    have hindex : cubic.index = 240 := by
      have hc := cubic.card_mul_index
      rw [cubic_card,product_card] at hc
      omega
    have hj := cubic.relIndex_dvd_index_of_normal J
    rw [←inf_relIndex_right,hi,relIndex_bot_left,hindex] at hj
    exact (show ¬ 9 ∣ 240 by decide) (h9.trans hj) |>.elim
  · have he : cubic ⊓ J = cubic := eq_of_le_of_card_ge inf_le_left (by rw [h3,cubic_card])
    exact he ▸ (show cubic ⊓ J ≤ J from inf_le_right)

/-- The first projection still has a cubic: the other factor has only one
power of three in its order. -/
theorem three_dvd_first (J : Subgroup Product) (h9 : 9 ∣ Nat.card J) :
    3 ∣ Nat.card (J.map (MonoidHom.fst S5 S3)) := by
  let f := (MonoidHom.fst S5 S3).subgroupMap J
  let g := (MonoidHom.snd S5 S3).comp J.subtype
  have hi : Function.Injective (f.prod g) := by
    intro x y he
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p => (p.1 : S5)) he)
      (congrArg (fun p : (J.map (MonoidHom.fst S5 S3)) × S3 => p.2) he)
  have hd := h9.trans (card_dvd_of_injective (f.prod g) hi)
  rw [Nat.card_prod] at hd
  have hs : Nat.card S3 = 6 := by
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  rw [hs] at hd
  have hthree : 3 ∣ Nat.card (J.map (MonoidHom.fst S5 S3)) * 2 := by
    obtain ⟨k,hk⟩ := hd
    exact ⟨k,by omega⟩
  exact (by decide : Nat.Coprime 3 2).dvd_mul_right.mp hthree

/-- The whole second factor occurs when the subgroup also contains a Sylow two-group. -/
theorem second_eq_top (J : Subgroup Product) (h9 : 9 ∣ Nat.card J)
    (P : Sylow 2 Product) (hP : (P : Subgroup Product) ≤ J) :
    J.map (MonoidHom.snd S5 S3) = ⊤ := by
  let B := J.map (MonoidHom.snd S5 S3)
  have hAB : alternatingGroup (Fin 3) ≤ B := by
    intro a ha
    exact ⟨(1,a),cubic_le_of_nine_dvd J h9 ⟨rfl,ha⟩,rfl⟩
  have hd : B.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hAB
  let Q := P.mapSurjective (f := MonoidHom.snd S5 S3) (fun a => ⟨(1,a),rfl⟩)
  have hQB : (Q : Subgroup S3) ≤ B := map_mono hP
  have hn : ¬ 2 ∣ B.index := fun hh => Q.not_dvd_index (hh.trans (index_dvd_of_le hQB))
  exact index_eq_one.mp ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right (fun he => hn (by rw [he])))

/-- The two-core of the actual Sylow overgroup lies in A5 times the identity. -/
theorem core_le_quintic (J : Subgroup Product) (h9 : 9 ∣ Nat.card J)
    (P : Sylow 2 Product) (hP : (P : Subgroup Product) ≤ J) :
    J.pCoreIn 2 ≤ (alternatingGroup (Fin 5)).prod (⊥ : Subgroup S3) := by
  let f := MonoidHom.fst S5 S3
  let P5 := P.mapSurjective (f := f) (fun a => ⟨(a,1),rfl⟩)
  have h5 := SymmetricFive.LocalTwoCore.core_le_alternating (J.map f) P5
    (map_mono hP) (three_dvd_first J h9)
  have hf := Alternating.FiveBorelCentralFactor.core_image_le f J
  let g := (MonoidHom.snd S5 S3).comp J.subtype
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨x,hx,he⟩ := (second_eq_top J h9 P hP).ge (mem_top a)
    exact ⟨⟨x,hx⟩,he⟩
  have hcore : pCore 2 S3 = ⊥ := by
    have he := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id S3)
      Function.surjective_id (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
    simpa using he.symm
  have hn : ((pCore 2 J).map g).Normal := Normal.map inferInstance g hg
  have hmap : (pCore 2 J).map g ≤ pCore 2 S3 :=
    le_sSup ⟨hn,pCore_isPGroup.map g⟩
  rw [hcore] at hmap
  rintro x ⟨y,hy,rfl⟩
  exact ⟨h5 (hf (mem_map_of_mem f (mem_map_of_mem J.subtype hy))),
    hmap (mem_map_of_mem g hy)⟩
/-- Its two-core has order at most four, retaining the whole subgroup. -/
theorem core_card_le_four (J : Subgroup Product) (h9 : 9 ∣ Nat.card J)
    (P : Sylow 2 Product) (hP : (P : Subgroup Product) ≤ J) :
    Nat.card (J.pCoreIn 2) ≤ 4 := by
  have hd := card_dvd_of_le (core_le_quintic J h9 P hP)
  have ha : Nat.card ((alternatingGroup (Fin 5)).prod (⊥ : Subgroup S3)) = 60 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,card_bot,mul_one,
      nat_card_alternatingGroup,Nat.card_fin]
    decide
  rw [ha] at hd
  obtain ⟨n,hn⟩ := (isPGroup_pCoreIn 2 J).exists_card_eq
  have hc : Nat.Coprime (Nat.card (J.pCoreIn 2)) 15 := by
    rw [hn]
    exact (by decide : Nat.Coprime 2 15).pow_left n
  exact Nat.le_of_dvd (by decide : 0 < 4) (hc.dvd_mul_right.mp
    (show Nat.card (J.pCoreIn 2) ∣ 4 * 15 from hd))

end Theory.SpecificGroups.SymmetricFiveThreeLocal
