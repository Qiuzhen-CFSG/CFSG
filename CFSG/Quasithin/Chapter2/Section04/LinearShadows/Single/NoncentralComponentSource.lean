module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NoncentralCoreSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.LocalFamily
public import Theory.GroupTheory.SylowNormalizedSupIndex
/-!
# The fixed natural block in the centralizer component

For the noncentral branch of 2.4.23(5), the outside coset moves the two fixed
modules noncommutatively. This gives the required normalizer bound. The actual
Sylow subgroup of the fixed block then supplies its intrinsic local-family
membership, so the index-two component theorem applies without assuming that
this Sylow is Sylow in the larger component.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G]

/-- The outside coset cannot normalize the elementary module it moves
noncommutatively, so the normalizer bound needs no ambient fusion theorem. -/
theorem fixed_module_normalizer_le
    (L S T : Subgroup G) {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (hi : S.relIndex T=2) (hSL : S≤normalizer (L:Set G))
    (x:G) (hxT:x∈T) (hxS:x∉S)
    (hnc : ¬ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer ((ChapterC.blockU L).map L.subtype : Set G)) :
    T ⊓ normalizer ((ChapterC.blockU L).map L.subtype : Set G) ≤ S := by
  let U := (ChapterC.blockU L).map L.subtype
  have hSU : S≤normalizer (U:Set G) := hSL.trans
    (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  rintro a ⟨haT,haN⟩
  by_contra haS
  have hax : a*x∈S := by
    apply ((S.subgroupOf T).mul_mem_iff_of_index_two hi
      (a:=(⟨a,haT⟩:T)) (b:=(⟨x,hxT⟩:T))).mpr
    change a∈S ↔ x∈S
    simp only [haS,hxS]
  have hxN : x ∈ normalizer (U:Set G) := by
    simpa only [inv_mul_cancel_left] using
      (normalizer (U:Set G)).mul_mem ((normalizer (U:Set G)).inv_mem haN) (hSU hax)
  apply hnc
  have he : U.map (MulAut.conj x⁻¹).toMonoidHom=U :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (U:Set G)).inv_mem hxN)
  let := hL.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map L.subtype
  exact he.le.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)

variable [Finite G]

/-- A normalized natural block is local at a two-group containing its
actual Sylow image. This uses the literal Sylow of L, not a Sylow of K. -/
theorem fixed_natural_mem_local_family
    (L S X : Subgroup G) {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (hS : IsPGroup 2 S) (hSL : S≤normalizer (L:Set G))
    (P : Sylow 2 L) (hPS : (P:Subgroup L).map L.subtype ≤ S)
    (hLX : L≤X) (hSX : S≤X) :
    L.subgroupOf X ∈ Chapter1.L X (S.subgroupOf X) := by
  obtain ⟨Q,hQ⟩ := hS.exists_sylow_sup_of_coprime_index L S hSL
    (P:Subgroup L) P.not_dvd_index hPS
  have hnot : ¬ ChapterC.IsAlternatingBlock L 3 := by
    intro h3
    have hc : 2^(n*2)=4 := by rw [←hL.module_card,h3.module_card_odd (by decide)]; norm_num
    have hn := hL.1
    have hlow : 16≤2^(n*2) := Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 4≤n*2)
    omega
  have hl := ChapterC.Section05.NormalizerControl.noncubic_mem_local_family L S
    (Or.inl ⟨n,hL⟩) hnot hSL Q hQ
  exact (Chapter1.mem_LIn_iff_subgroupOf hSX hLX).mp ⟨hLX,hl⟩

/-- The source fixed-block packet and the actual centralizer Sylow packet
supply the component without a separate local-family or normalizer premise. -/
theorem fixed_pair_isComponent_of_sylow_block
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (L R S T : Subgroup G) {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (hST : S ≤ T) (hi : S.relIndex T = 2)
    (hcore : pCore 2 L = ChapterC.blockU L)
    (P : Sylow 2 L) (hP : (P:Subgroup L).map L.subtype=R) (hRS:R≤S)
    (hTR : T ≤ normalizer (R : Set G))
    (hSL : S ≤ normalizer (L : Set G)) (x : G) (hxT : x ∈ T) (hxS : x ∉ S)
    (hnc : ¬ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer ((ChapterC.blockU L).map L.subtype : Set G)) :
    let K := L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom
    let X := K ⊔ T
    twoCore X ≠ ⊥ →
      (∃ Q : Sylow 2 X, (Q : Subgroup X).map X.subtype = T) →
      IsComponent X (K.subgroupOf X) := by
  dsimp only
  let K := L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom
  let X := K ⊔ T
  intro hQne hSylow
  have hUR : (ChapterC.blockU L).map L.subtype≤R := by
    rw [←hcore,←hP]
    exact pCoreIn_le_sylow L P
  have hRL : R≤L := hP ▸ map_subtype_le _
  have hTS := fixed_module_normalizer_le L S T hL hi hSL x hxT hxS hnc
  have hlocal : L.subgroupOf X ∈ Chapter1.L X (S.subgroupOf X) := by
    obtain ⟨Q,hQ⟩ := hSylow
    have hT : IsPGroup 2 T := hQ ▸ Q.isPGroup'.map X.subtype
    exact fixed_natural_mem_local_family L S X hL (hT.to_le hST) hSL P
      (hP.le.trans hRS) (le_sup_left.trans le_sup_left) (hST.trans le_sup_right)
  exact fixed_pair_isComponent hG L R S T hL hST hi hcore hUR hRL hTR hTS hSL
    x hxT hxS hnc hQne hSylow hlocal
end CFSG.Quasithin.Chapter2.LinearShadows.Single
