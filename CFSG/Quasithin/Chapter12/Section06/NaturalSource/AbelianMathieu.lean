module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianModels
public import Theory.Mathieu.M22.CubicHexad
public import Theory.GroupTheory.NormalSylowQuotientAction.InvariantLift

/-!
# The original Mathieu component exclusions

A perfect subgroup of M fixing the original point centralizes the full V,
because its permutation image lies in the solvable point stabilizer.
Every three-element of that subgroup lies in O^{3′}(M)=L, hence in the
literal C_L(V)=O₂(L), a contradiction. Taking the solvable residual shows
that a subgroup of M fixing the point has no perfect quotient of order
divisible by three.

For a T-invariant K with central quotient M₂₂, the native invariant cubic
hexad pair lifts through both Z(K/O₂(K)) and O₂(K). Each lift together
with the original T is solvable, so 12.6.29 places it in M. Their join
maps onto the perfect hexad group containing A₆. The preceding obstruction
excludes this join. This treats M₂₂ and its genuine triple cover together,
without discarding either quotient kernel or assuming a selected component
from the contrary nonabelian branch.

Earlier Sylow, point, TI, intersection and nonsingular-centralizer geometry
remain explicit. Source: Aschbacher--Smith 12.6.29--31, printed pp.835--836.
The concrete cubic hexad pair is also used in source 14.3.6(6), p.994.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open Chapter15.Section03.AbelianAmalgam.GenerationOne
private theorem symmetric_three_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [range_subtype, ←alternatingGroup_eq_sign_ker]

private theorem solvable_of_symmetric_three_core {X : Type*} [Group X] [Finite X]
    (e : (X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) : Group.IsSolvable X := by
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := symmetric_three_solvable
  let : Group.IsSolvable (X ⧸ pCore 2 X) := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 X) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr ⟨inferInstance,inferInstance⟩

private theorem central_lift_invariant {C X : Type*} [Group C] [Group X]
    (e : (C ⧸ center C) ≃* X) (P : Subgroup C) (J : Subgroup X)
    (hinv : ∀ b : MulAut X,
      (P.map (e.toMonoidHom.comp (QuotientGroup.mk' (center C)))).map b.toMonoidHom =
        P.map (e.toMonoidHom.comp (QuotientGroup.mk' (center C))) → J.map b.toMonoidHom = J)
    (a : MulAut C) (ha : P.map a.toMonoidHom = P) :
    (J.comap (e.toMonoidHom.comp (QuotientGroup.mk' (center C)))).map a.toMonoidHom =
      J.comap (e.toMonoidHom.comp (QuotientGroup.mk' (center C))) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let b := (MulAut.congr e) ((center C).quotientAut a)
  have he (c : C) : b (q c) = q (a c) := by
    simp only [b,q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.congr_apply,
      MulEquiv.trans_apply,e.symm_apply_apply,quotientAut_apply_mk]
  have hb : (P.map q).map b.toMonoidHom = P.map q := by
    rw [map_map,show b.toMonoidHom.comp q = q.comp a.toMonoidHom from MonoidHom.ext he,
      ←map_map,ha]
  have hJ := hinv b hb
  ext c
  rw [mem_map_equiv]
  change q (a.symm c) ∈ J ↔ q c ∈ J
  have hx : q c = b (q (a.symm c)) := by rw [he,a.apply_symm_apply]
  constructor
  · intro h
    rw [hx,←hJ]
    exact mem_map_of_mem b.toMonoidHom h
  · intro h
    have hb : b (q (a.symm c)) ∈ J.map b.toMonoidHom := by rwa [hJ,←hx]
    simpa only [mem_map_equiv,b.symm_apply_apply] using hb

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)

include hz hTV hTz hTI in
/-- A perfect subgroup of M fixing the original Sylow-fixed point has no
three-elements: its trivial point action and O^{3′}(M)=L place such an
element in the original two-core. -/
theorem SourceHypothesis.original_perfect_point_three_free
    (A : Subgroup G) [Group.IsPerfect A]
    (hAM : A ≤ M L) (hAz : A ≤ (D.fullSetup hZ T z).Gz) :
    ¬ 3 ∣ Nat.card A := by
  intro hd
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 hd
  have hc := S.original_perfect_point_subgroup_centralizes D hZ z hz hTV hTz hTI A hAM hAz
  have hp : (⟨a.val,hAM a.property⟩ : M L) ^ (3 ^ 1) = 1 := by
    apply Subtype.ext
    change a.val ^ (3 ^ 1) = 1
    simpa only [pow_one,←ha,Subgroup.coe_pow,Subgroup.coe_one] using congrArg Subtype.val (pow_orderOf_eq_one a)
  have hm : a.val ∈ (primeToResidual 3 (M L)).map (M L).subtype :=
    mem_map_of_mem _ (mem_primeToResidual_of_pow hp)
  rw [S.normalizer_primeToResidual D] at hm
  have hq : a.val ∈ L.pCoreIn 2 := by
    rw [←S.centralizer_eq_core]
    exact ⟨hm,hc a.property⟩
  obtain ⟨n,hn⟩ := (isPGroup_pCoreIn 2 L).exists_orderOf_dvd_pow ⟨a.val,hq⟩
  rw [orderOf_mk,orderOf_coe,ha] at hn
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hn)

include hz hTV hTz hTI in
/-- No subgroup of the original point overlap has a perfect quotient of
order divisible by three. Its solvable residual still maps onto that quotient. -/
theorem SourceHypothesis.original_point_no_perfect_three_image
    (B : Subgroup G) (hBM : B ≤ M L) (hBz : B ≤ (D.fullSetup hZ T z).Gz)
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (f : B →* X) (hf : Function.Surjective f) (h3 : 3 ∣ Nat.card X) : False := by
  let A := (solvableResidual B).map B.subtype
  let : Group.IsPerfect A := Group.IsPerfect.map B.subtype
  have hA : ¬ 3 ∣ Nat.card A := S.original_perfect_point_three_free D hZ z hz hTV hTz hTI
    A ((map_subtype_le _).trans hBM) ((map_subtype_le _).trans hBz)
  have hm : (solvableResidual B).map f = ⊤ := by
    rw [map_solvableResidual_eq f hf,solvableResidual_eq_top]
  have hr : Nat.card X ∣ Nat.card (solvableResidual B) := by
    have hh := (solvableResidual B).card_map_dvd f
    rwa [hm,card_top] at hh
  have he : Nat.card A = Nat.card (solvableResidual B) := card_map_of_injective B.subtype_injective
  exact hA (he.symm ▸ (h3.trans hr))


include hz hTV hTz hbound hTI hns in
/-- Exclude a Mathieu central quotient of any original T-invariant subgroup
of H. Both the two-core and the central quotient kernel are retained. -/
theorem SourceHypothesis.original_escaping_mathieuCentral_impossible
    {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) (hKH : K ≤ H)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* Sporadic.Mathieu.M22) : False := by
  let C := K ⧸ pCore 2 K
  let qK : K →* C := QuotientGroup.mk' (pCore 2 K)
  let qC : C →* Sporadic.Mathieu.M22 := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let q := qC.comp qK
  have hqC : Function.Surjective qC := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hq : Function.Surjective q := hqC.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let PC := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K))
  let PQ := P.mapSurjective hq
  obtain ⟨J₁,J₂,_,_,_,_,hinv,⟨e₁⟩,⟨e₂⟩,hperf,j,hj⟩ :=
    Sporadic.Mathieu.M22CubicHexad.exists_invariant_cubic_hexad_pair PQ
  let B₁ := (J₁.comap q).map K.subtype
  let B₂ := (J₂.comap q).map K.subtype
  have hlocal (J : Subgroup Sporadic.Mathieu.M22)
      (hs : Group.IsSolvable J)
      (hi : ∀ a : MulAut Sporadic.Mathieu.M22,
        (PQ : Subgroup Sporadic.Mathieu.M22).map a.toMonoidHom = PQ → J.map a.toMonoidHom = J) :
      (J.comap q).map K.subtype ≤ M L := by
    let := hs
    have hk : qC.ker = center C := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    let : Group.IsSolvable qC.ker := hk ▸ inferInstance
    let : Group.IsSolvable (J.comap qC) := isSolvable_comap_of_solvable_ker qC J
    have hiC : ∀ a : MulAut C, (PC : Subgroup C).map a.toMonoidHom = PC →
        (J.comap qC).map a.toMonoidHom = J.comap qC := by
      apply central_lift_invariant e (PC : Subgroup C) J
      intro b hb
      apply hi b
      simpa only [PC,PQ,Sylow.coe_mapSurjective,map_map] using hb
    have hsB := NormalSylowQuotientAction.solvable_lift_sup_of_sylow_invariant
      T K hTK (MulEquiv.refl C) P hP (J.comap qC) hiC
    have he : ((J.comap qC).comap ((MulEquiv.refl C).toMonoidHom.comp qK)).map K.subtype =
        (J.comap q).map K.subtype := rfl
    rw [he] at hsB
    let := hsB
    exact le_sup_left.trans (S.original_solvable_overgroup_le D hZ z hz hTV hTz hbound hTI hns
      (show (T : Subgroup G) ≤ (J.comap q).map K.subtype ⊔ (T : Subgroup G) from le_sup_right))
  have hB₁ : B₁ ≤ M L := hlocal J₁ (solvable_of_symmetric_three_core e₁) (fun a ha => (hinv a ha).1)
  have hB₂ : B₂ ≤ M L := hlocal J₂ (solvable_of_symmetric_three_core e₂) (fun a ha => (hinv a ha).2)
  let J := J₁ ⊔ J₂
  let B := (J.comap q).map K.subtype
  have hB : B = B₁ ⊔ B₂ := by
    dsimp only [B,B₁,B₂,J]
    rw [←comap_sup_eq q J₁ J₂ hq,Subgroup.map_sup]
  have hBM : B ≤ M L := hB ▸ sup_le hB₁ hB₂
  have hBK : B ≤ K := map_subtype_le _
  let f : B →* J := (q.subgroupComap J).comp
    (((J.comap q).equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom)
  have hf : Function.Surjective f := (q.subgroupComap_surjective_of_surjective J hq).comp
    ((J.comap q).equivMapOfInjective K.subtype K.subtype_injective).symm.surjective
  let : Group.IsPerfect J := hperf
  have h3 : 3 ∣ Nat.card J := by
    have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup,Nat.card_fin]
      decide
    exact (show 3 ∣ Nat.card (alternatingGroup (Fin 6)) by rw [hc]; decide).trans
      (card_dvd_of_injective j hj)
  exact S.original_point_no_perfect_three_image D hZ z hz hTV hTz hTI B hBM
    (hBK.trans (hKH.trans hH.2.1)) f hf h3


include hz hTV hTz hbound hTI hns in
/-- Both genuine Mathieu carriers are impossible for the original escaping
T-invariant component, with its central kernel retained. -/
theorem SourceHypothesis.original_escaping_mathieu_impossible
    {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) (hKH : K ≤ H)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Models.M22Triple)) : False := by
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    exact S.original_escaping_mathieuCentral_impossible D hZ z hz hTV hTz hbound hTI hns hH hKH hTK
      ((centralQuotientEquiv e).trans
        (CoverModels.centerQuotientEquiv Sporadic.Mathieu.m22_center_eq_bot).symm)
  · obtain ⟨e⟩ := hm
    exact S.original_escaping_mathieuCentral_impossible D hZ z hz hTV hTz hbound hTI hns hH hKH hTK
      ((centralQuotientEquiv e).trans Sporadic.Mathieu.M22TripleCover.centralQuotientEquiv)


end CFSG.Quasithin.Chapter12.Section06
