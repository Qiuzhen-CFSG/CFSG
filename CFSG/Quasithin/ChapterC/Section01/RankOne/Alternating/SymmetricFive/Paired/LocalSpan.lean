module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.ResidualGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.LocalGeometry
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The literal local conjugate span on a paired S₅ factor

The prescribed residual factor maps to its A₅ axis. Its intersection with
the original maximal overgroup supplies an actual lift of the marked even
cubic. Conjugating the Baumann product by this lift generates precisely the
S₄ factor times the unchanged opposite four-group. The kernel containment
keeps the lift in the original maximal overgroup.

Source: Aschbacher--Smith C.1.24 and E.2.3(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open ChapterB.Offenders

theorem prod_sup_prod (A B C D : Subgroup Sym) :
    A.prod C ⊔ B.prod D = (A ⊔ B).prod (C ⊔ D) := by
  apply le_antisymm (sup_le (prod_mono le_sup_left le_sup_left)
    (prod_mono le_sup_right le_sup_right))
  rw [prod_le_iff,Subgroup.map_sup,Subgroup.map_sup]
  constructor
  · apply sup_le
    · rintro _ ⟨a,ha,rfl⟩; exact mem_sup_left ⟨ha,C.one_mem⟩
    · rintro _ ⟨b,hb,rfl⟩; exact mem_sup_right ⟨hb,D.one_mem⟩
  · apply sup_le
    · rintro _ ⟨c,hc,rfl⟩; exact mem_sup_left ⟨A.one_mem,hc⟩
    · rintro _ ⟨d,hd,rfl⟩; exact mem_sup_right ⟨B.one_mem,hd⟩

theorem local_conjugate_transposition_product (a b : Sym) :
    (((D 5).map (MulAut.conj a).toMonoidHom).prod
      ((D 5).map (MulAut.conj b).toMonoidHom)) ⊔
    ((((D 5).map (MulAut.conj a).toMonoidHom).prod
      ((D 5).map (MulAut.conj b).toMonoidHom)).map
        (MulAut.conj (a * localCubic * a⁻¹,(1 : Sym))).toMonoidHom) =
    (pointFour.map (MulAut.conj a).toMonoidHom).prod
      ((D 5).map (MulAut.conj b).toMonoidHom) := by
  have hc (A B : Subgroup Sym) (x : Sym) :
      (A.prod B).map (MulAut.conj (x,(1 : Sym))).toMonoidHom =
        (A.map (MulAut.conj x).toMonoidHom).prod B := by
    ext g
    constructor
    · rintro ⟨g,hg,rfl⟩; exact ⟨⟨g.1,hg.1,rfl⟩,by simpa [MulAut.conj_apply] using hg.2⟩
    · rintro ⟨⟨h,hh,he⟩,hg⟩
      exact ⟨(h,g.2),⟨hh,hg⟩,Prod.ext he (by simp [MulAut.conj_apply])⟩
  rw [hc,prod_sup_prod,sup_idem,local_two_conjugate_four_groups_generate]

variable {G H : Type*} [Group G] [Group H]

theorem mapped_first_local_span
    (q : G →* H) (j : Sym × Sym →* H)
    (S K M : Subgroup G) (hkerM : q.ker ≤ M)
    (a b : Sym)
    (hS : S.map q = (((D 5).map (MulAut.conj a).toMonoidHom).prod
      ((D 5).map (MulAut.conj b).toMonoidHom)).map j)
    (hK : K.map q = ((alternatingGroup (Fin 5)).prod (⊥ : Subgroup Sym)).map j)
    (hM : (M.map q).comap (j.comp (MonoidHom.inl Sym Sym)) =
      pointFour.map (MulAut.conj a).toMonoidHom) :
    (conjugateSpanBy S (K ⊓ M)).map q =
      ((pointFour.map (MulAut.conj a).toMonoidHom).prod
        ((D 5).map (MulAut.conj b).toMonoidHom)).map j := by
  let A := (D 5).map (MulAut.conj a).toMonoidHom
  let B := (D 5).map (MulAut.conj b).toMonoidHom
  let C := pointFour.map (MulAut.conj a).toMonoidHom
  have hAC : A ≤ C := by
    change _ ≤ pointFour.map (MulAut.conj a).toMonoidHom
    rw [←local_two_conjugate_four_groups_generate a]
    exact le_sup_left
  have hkC {x : G} (hx : x ∈ K ⊓ M) :
      ∃ k : Sym, k ∈ C ∧ q x = j (k,1) := by
    obtain ⟨k,hk,hxk⟩ := (SetLike.ext_iff.mp hK (q x)).mp (mem_map_of_mem q hx.1)
    have hk' : k.2 = 1 := hk.2
    have he : q x = j (k.1,1) := hxk.symm.trans (congrArg j (Prod.ext rfl hk'))
    refine ⟨k.1,?_,he⟩
    change k.1 ∈ pointFour.map (MulAut.conj a).toMonoidHom
    rw [←hM]
    change j (k.1,1) ∈ M.map q
    exact he ▸ mem_map_of_mem q hx.2
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro _ ⟨g,hg,s,hs,rfl⟩
    obtain ⟨k,hk,hqk⟩ := hkC hg
    obtain ⟨v,hv,hvs⟩ := (SetLike.ext_iff.mp hS (q s)).mp (mem_map_of_mem q hs)
    change q (g*s*g⁻¹) ∈ (C.prod B).map j
    rw [map_mul,map_mul,map_inv,hqk,←hvs,←map_mul,←map_inv,←map_mul]
    exact mem_map_of_mem j ⟨C.mul_mem (C.mul_mem hk (hAC hv.1)) (C.inv_mem hk),by
      change (1 * v.2 * 1) ∈ B
      simpa only [one_mul,mul_one] using (show v.2 ∈ B from hv.2)⟩
  · have heven : a * localCubic * a⁻¹ ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_mul,map_inv,
        Equiv.Perm.mem_alternatingGroup.mp localCubic_even,mul_one,mul_inv_cancel]
    obtain ⟨g,hg,hqg⟩ : ∃ g ∈ K, q g = j (a * localCubic * a⁻¹,1) := by
      exact (SetLike.ext_iff.mp hK _).mpr (mem_map_of_mem j ⟨heven,one_mem _⟩)
    have hgM : g ∈ M := by
      apply (show (M.map q).comap q ≤ M from by rw [comap_map_eq_self hkerM])
      change q g ∈ M.map q
      rw [hqg]
      have hc : a * localCubic * a⁻¹ ∈ C := mem_map_of_mem (MulAut.conj a).toMonoidHom localCubic_mem_pointFour
      have hcm := (SetLike.ext_iff.mp hM _).mpr hc
      exact hcm
    let I := conjugateSpanBy S (K ⊓ M)
    have hconjI : S.map (MulAut.conj g).toMonoidHom ≤ I := by
      rintro _ ⟨s,hs,rfl⟩
      exact subset_closure ⟨g,⟨hg,hgM⟩,s,hs,rfl⟩
    have hconj : (S.map (MulAut.conj g).toMonoidHom).map q =
        (((A.prod B).map (MulAut.conj (a*localCubic*a⁻¹,(1:Sym))).toMonoidHom).map j) := by
      have h₁ : (S.map (MulAut.conj g).toMonoidHom).map q =
          (S.map q).map (MulAut.conj (q g)).toMonoidHom := by
        rw [map_map,map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply]
      rw [h₁,hS,hqg,map_map,map_map]
      congr 1
      ext x
      change j (a*localCubic*a⁻¹,1) * j x * (j (a*localCubic*a⁻¹,1))⁻¹ =
        j ((a*localCubic*a⁻¹,1) * x * (a*localCubic*a⁻¹,1)⁻¹)
      rw [map_mul,map_mul,map_inv]
    have hh := sup_le (map_mono (f:=q) (le_conjugateSpanBy S (K ⊓ M))) (map_mono (f:=q) hconjI)
    rw [hS,hconj,←Subgroup.map_sup,local_conjugate_transposition_product] at hh
    exact hh
theorem prod_map_swap (A B : Subgroup Sym) (j : Sym × Sym →* H) :
    (A.prod B).map (j.comp (MulEquiv.prodComm : Sym × Sym ≃* Sym × Sym).toMonoidHom) =
      (B.prod A).map j := by
  ext x
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨(g.2,g.1),⟨hg.2,hg.1⟩,rfl⟩
  · rintro ⟨g,hg,rfl⟩
    exact ⟨(g.2,g.1),⟨hg.2,hg.1⟩,rfl⟩

theorem mapped_second_local_span
    (q : G →* H) (j : Sym × Sym →* H)
    (S K M : Subgroup G) (hkerM : q.ker ≤ M)
    (a b : Sym)
    (hS : S.map q = (((D 5).map (MulAut.conj a).toMonoidHom).prod
      ((D 5).map (MulAut.conj b).toMonoidHom)).map j)
    (hK : K.map q = ((⊥ : Subgroup Sym).prod (alternatingGroup (Fin 5))).map j)
    (hM : (M.map q).comap (j.comp (MonoidHom.inr Sym Sym)) =
      pointFour.map (MulAut.conj b).toMonoidHom) :
    (conjugateSpanBy S (K ⊓ M)).map q =
      (((D 5).map (MulAut.conj a).toMonoidHom).prod
        (pointFour.map (MulAut.conj b).toMonoidHom)).map j := by
  have h := mapped_first_local_span q
    (j.comp (MulEquiv.prodComm : Sym × Sym ≃* Sym × Sym).toMonoidHom) S K M hkerM b a
    (by simpa only [prod_map_swap] using hS)
    (by simpa only [prod_map_swap] using hK)
    (by
      have hs : (MulEquiv.prodComm : Sym × Sym ≃* Sym × Sym).toMonoidHom.comp
          (MonoidHom.inl Sym Sym) = MonoidHom.inr Sym Sym := by ext x : 1; simp
      simpa only [MonoidHom.comp_assoc,hs] using hM)
  simpa only [prod_map_swap] using h
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
