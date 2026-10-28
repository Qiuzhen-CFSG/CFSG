module

public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Defs
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.AmbientQuotient
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Transport of the rank-one Cartan action argument

Source: the field-automorphism step in Aschbacher–Smith F.1.3(5), p.260.
Cartan quadratic rigidity transports along genuine group equivalences and
lifts through the two-core. The literal quotient sends a Sylow complement
to a complement in the quotient Sylow normalizer. Its odd order makes the
projection injective on it; consequently pointwise fixation downstairs
implies pointwise fixation upstairs.

The ambient adapter uses the normalizer's actual conjugation homomorphism.
These are conditional transport results: no concrete model's automorphism
classification or rigidity is assumed to have been proved here.
-/

public section
open Subgroup Subgroup.OddHall
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {S : Subgroup G}

/-- Apply intrinsic rigidity to actual ambient conjugation, with the supplied
Sylow embedding and the original subgroup complement. -/
theorem CartanQuadraticRigidity.ambient {A : Subgroup G} [Finite A]
    (hr : CartanQuadraticRigidity A) (T : Sylow 2 A)
    (hT : (T : Subgroup A).map A.subtype = S ⊓ A)
    {D : Subgroup G} (hD : D ≤ borel A S) (ho : Nat.Coprime 2 (Nat.card D))
    (hd : Disjoint (S ⊓ A) D) (hs : (S ⊓ A) ⊔ D = borel A S)
    {g : G} (hg : g ∈ normalizer (A : Set G)) (hog : Odd (orderOf g))
    (hgT : g ∈ normalizer ((S ⊓ A : Subgroup G) : Set G))
    (hgD : g ∈ normalizer (D : Set G))
    (hq : ∀ x ∈ D, g * (g * x * g⁻¹ * x⁻¹) * g⁻¹ = g * x * g⁻¹ * x⁻¹) :
    ∀ x ∈ D, g * x * g⁻¹ = x := by
  let a := A.normalizerMonoidHom ⟨g,hg⟩
  let E := D.subgroupOf A
  have hDA : D ≤ A := hD.trans (borel_le _ _)
  have hEA : E.map A.subtype = D := map_subgroupOf_eq_of_le hDA
  have hNA : (normalizer (T : Set A)).map A.subtype = borel A S := by
    change (sylowNormalizer T).map A.subtype = _
    rw [← borel_subgroupOf_eq_sylowNormalizer A S T hT]
    exact map_subgroupOf_eq_of_le (borel_le _ _)
  have ha_map (K : Subgroup A) :
      (K.map a.toMonoidHom).map A.subtype = (K.map A.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hEN : E ≤ normalizer (T : Set A) := by
    apply (map_le_map_iff_of_injective A.subtype_injective).mp
    rw [hEA, hNA]
    exact hD
  have hEt : Disjoint (T : Subgroup A) E := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    apply Subtype.ext
    have ht : (x : G) ∈ S ⊓ A := hT ▸ mem_map_of_mem A.subtype hx.1
    exact disjoint_iff_inf_le.mp hd ⟨ht, hx.2⟩
  have hEs : (T : Subgroup A) ⊔ E = normalizer (T : Set A) := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, hT, hEA, hNA, hs]
  have hEt' : (T : Subgroup A).map a.toMonoidHom = T := by
    apply map_injective A.subtype_injective
    rw [ha_map, hT]
    exact mem_normalizer_iff_map_conj_eq.mp hgT
  have hEE : E.map a.toMonoidHom = E := by
    apply map_injective A.subtype_injective
    rw [ha_map, hEA]
    exact mem_normalizer_iff_map_conj_eq.mp hgD
  have hao : Odd (orderOf a) := by
    apply hog.of_dvd_nat
    exact (orderOf_map_dvd A.normalizerMonoidHom ⟨g,hg⟩).trans (by simp)
  have hEo : Nat.Coprime 2 (Nat.card E) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDA).toEquiv]
  have hf := hr T E hEN hEo hEt hEs a hao hEt' hEE (by
    intro x hx
    exact Subtype.ext (hq x.val hx))
  intro x hx
  exact congrArg Subtype.val (hf ⟨x,hDA hx⟩ hx)

variable {H : Type*} [Group H] [Finite H]

/-- Rigidity in the actual quotient by O₂(H) implies rigidity in H. -/
theorem CartanQuadraticRigidity.of_twoCore_quotient
    (hr : CartanQuadraticRigidity (H ⧸ pCore 2 H)) : CartanQuadraticRigidity H := by
  intro T D hDN ho hd hs a hao haT haD hquad
  let q := QuotientGroup.mk' (pCore 2 H)
  let b := (pCore 2 H).quotientAut a
  let E := D.map q
  let U := quotientSylow T
  have hU : (T : Subgroup H).map q = (U : Subgroup _) := rfl
  have hN : (normalizer (T : Set H)).map q = normalizer (U : Set _) :=
    quotientSylow_normalizer_map T
  have hEN : E ≤ normalizer (U : Set _) := hN ▸ Subgroup.map_mono hDN
  have hEo : Nat.Coprime 2 (Nat.card E) := ho.of_dvd_right (D.card_map_dvd q)
  have hEd : Disjoint (U : Subgroup _) E := by
    apply disjoint_iff_inf_le.mpr
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz.2
    have ht : x ∈ (T : Subgroup H) := by
      rw [← quotientSylow_comap T]
      exact hz.1
    have hx1 : x = 1 := disjoint_iff_inf_le.mp hd ⟨ht,hx⟩
    simp only [hx1, map_one, mem_bot]
  have hEs : (U : Subgroup _) ⊔ E = normalizer (U : Set _) := by
    rw [← hU, ← Subgroup.map_sup, hs, hN]
  have hb : Odd (orderOf b) := hao.of_dvd_nat (orderOf_map_dvd _ _)
  have hmap (K : Subgroup H) :
      (K.map q).map b.toMonoidHom = (K.map a.toMonoidHom).map q := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact quotientAut_apply_mk _ a x
  have hbU : (U : Subgroup _).map b.toMonoidHom = U := by
    rw [← hU, hmap, haT]
  have hbE : E.map b.toMonoidHom = E := by
    change (D.map q).map b.toMonoidHom = D.map q
    rw [hmap, haD]
  have hf := hr U E hEN hEo hEd hEs b hb hbU hbE (by
    rintro z ⟨x,hx,rfl⟩
    change b (b (q x) * (q x)⁻¹) = b (q x) * (q x)⁻¹
    have hbq (y : H) : b (q y) = q (a y) := quotientAut_apply_mk _ a y
    rw [hbq, ← map_inv, ← map_mul, hbq, hquad x hx])
  intro x hx
  have he : q (a x) = q x := by
    simpa only [b, q, quotientAut_apply_mk] using hf (q x) (mem_map_of_mem q hx)
  have hk : a x * x⁻¹ ∈ pCore 2 H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (a x * x⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hDk : a x * x⁻¹ ∈ D :=
    D.mul_mem (haD ▸ mem_map_of_mem a.toMonoidHom hx) (D.inv_mem hx)
  have hkT : a x * x⁻¹ ∈ (T : Subgroup H) := pCore_isPGroup.le_sylow_of_normal T hk
  exact mul_inv_eq_one.mp (disjoint_iff_inf_le.mp hd ⟨hkT,hDk⟩)

variable {K : Type*} [Group K]

/-- Transport rigidity along an actual multiplicative equivalence. -/
theorem CartanQuadraticRigidity.of_equiv (e : H ≃* K)
    (hr : CartanQuadraticRigidity K) : CartanQuadraticRigidity H := by
  intro T D hDN ho hd hs a hao haT haD hquad
  let U := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let E := D.map e.toMonoidHom
  let b := MulAut.congr e a
  have hU : (T : Subgroup H).map e.toMonoidHom = (U : Subgroup K) := rfl
  have hN : (normalizer (T : Set H)).map e.toMonoidHom = normalizer (U : Set K) :=
    Subgroup.map_equiv_normalizer_eq _ e
  have hEN : E ≤ normalizer (U : Set K) := hN ▸ Subgroup.map_mono hDN
  have hEo : Nat.Coprime 2 (Nat.card E) := by
    rwa [← Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
  have hEd : Disjoint (U : Subgroup K) E := disjoint_map e.injective hd
  have hEs : (U : Subgroup K) ⊔ E = normalizer (U : Set K) := by
    rw [← hU, ← Subgroup.map_sup, hs, hN]
  have hb : Odd (orderOf b) := by rwa [(MulAut.congr e).orderOf_eq]
  have hbq (x : H) : b (e x) = e (a x) := by
    change e (a (e.symm (e x))) = e (a x)
    rw [e.symm_apply_apply]
  have hmap (V : Subgroup H) :
      (V.map e.toMonoidHom).map b.toMonoidHom = (V.map a.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact hbq x
  have hbU : (U : Subgroup K).map b.toMonoidHom = U := by
    rw [← hU, hmap, haT]
  have hbE : E.map b.toMonoidHom = E := by
    change (D.map e.toMonoidHom).map b.toMonoidHom = D.map e.toMonoidHom
    rw [hmap, haD]
  have hf := hr U E hEN hEo hEd hEs b hb hbU hbE (by
    rintro z ⟨x,hx,rfl⟩
    change b (b (e x) * (e x)⁻¹) = b (e x) * (e x)⁻¹
    rw [hbq, ← map_inv, ← map_mul, hbq, hquad x hx])
  intro x hx
  apply e.injective
  rw [← hbq]
  exact hf (e x) (mem_map_of_mem e.toMonoidHom hx)

end CFSG.Quasithin.ChapterF.Source
