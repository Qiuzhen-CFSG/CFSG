module
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# A central complement modulo the core of a Sylow overgroup

Let H contain a Sylow p-subgroup of G, and let A normalize H. The p-core
of HA lies in that Sylow subgroup, so normality gives Oₚ(HA)=Oₚ(H).
If H and A are disjoint and A has central image modulo this core,
multiplication induces (H/Oₚ(H)) × A ≃ HA/Oₚ(HA). The equivalence retains
both inclusions on representatives. For p=2 and odd A, every element
whose square is in the core already lies in H.

This is the finite-group quotient calculation used in Aschbacher–Smith
5.1.17, printed p.641 (refs/quasithin.pdf). The statements only need the
displayed Sylow and complement hypotheses, not the ambient classification.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A normalized Sylow overgroup retains its prime core after adjoining the normalizer. -/
theorem pCoreIn_sup_eq_of_sylow_le {p : ℕ} {T : Sylow p G} {H A : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hAH : A ≤ normalizer (H : Set G)) :
    (H ⊔ A).pCoreIn p = H.pCoreIn p := by
  have hQT : (H ⊔ A).pCoreIn p ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le (hTH.trans le_sup_left)]
      using pCoreIn_le_sylow (H ⊔ A) (T.subtype (hTH.trans le_sup_left))
  exact le_antisymm
    ((le_inf (hQT.trans hTH) le_rfl).trans (inf_pCoreIn_le_of_le p le_sup_left))
    (pCoreIn_mono_of_normalizes le_sup_left (sup_le H.le_normalizer hAH))

/-- The central disjoint complement gives a product after quotienting by the prime core,
with the original inclusions on representatives. -/
theorem exists_pCoreQuotient_product_of_sylow_le {p : ℕ} {T : Sylow p G} {H A : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hAH : A ≤ normalizer (H : Set G))
    (hd : Disjoint H A)
    (hc : (A.subgroupOf (H ⊔ A)).map (QuotientGroup.mk' (pCore p (H ⊔ A : Subgroup G))) ≤
      center ((H ⊔ A : Subgroup G) ⧸ pCore p (H ⊔ A : Subgroup G))) :
    ∃ e : ((H ⧸ pCore p H) × A) ≃*
        ((H ⊔ A : Subgroup G) ⧸ pCore p (H ⊔ A : Subgroup G)),
      ∀ (h : H) (a : A),
        e (QuotientGroup.mk' (pCore p H) h, a) =
          QuotientGroup.mk' (pCore p (H ⊔ A : Subgroup G))
            ⟨(h : G) * (a : G), mul_mem_sup h.property a.property⟩ := by
  let J := H ⊔ A
  let q := QuotientGroup.mk' (pCore p J)
  let hJ : H ≤ J := le_sup_left
  let aJ : A ≤ J := le_sup_right
  have hcore := pCoreIn_sup_eq_of_sylow_le hTH hAH
  have hQH : pCore p H ≤ (pCore p J).comap (inclusion hJ) := by
    intro h hh
    have hm : (h : G) ∈ J.pCoreIn p := hcore.symm ▸ mem_map_of_mem H.subtype hh
    obtain ⟨x, hx, he⟩ := hm
    change inclusion hJ h ∈ pCore p J
    exact (Subtype.ext he : x = inclusion hJ h) ▸ hx
  let l : (H ⧸ pCore p H) →* (J ⧸ pCore p J) :=
    QuotientGroup.map (pCore p H) (pCore p J) (inclusion hJ) hQH
  let r : A →* (J ⧸ pCore p J) := q.comp (inclusion aJ)
  have hcomm : ∀ h a, Commute (l h) (r a) := by
    intro h a
    exact (mem_center_iff.mp (hc (mem_map_of_mem q a.property)) (l h))
  let f := l.noncommCoprod r hcomm
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    rintro ⟨x,a⟩ hx
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (pCore p H) x
    have he : q (inclusion hJ h * inclusion aJ a) = 1 := by
      change q (inclusion hJ h) * q (inclusion aJ a) = 1 at hx
      rwa [map_mul]
    have hmem : (h : G) * (a : G) ∈ H.pCoreIn p := by
      rw [← hcore]
      exact mem_map_of_mem J.subtype ((QuotientGroup.eq_one_iff _).mp he)
    have haH : (a : G) ∈ H := (H.mul_mem_cancel_left h.property).mp ((pCoreIn_le p H) hmem)
    have ha1 : a = 1 := Subtype.ext (Subgroup.disjoint_def.mp hd haH a.property)
    subst a
    have hh : h ∈ pCore p H := by
      simp only [Subgroup.coe_one, mul_one] at hmem
      obtain ⟨h',hh',he'⟩ := hmem
      exact (Subtype.ext he' : h' = h) ▸ hh'
    exact Prod.ext ((QuotientGroup.eq_one_iff h).mpr hh) rfl
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    intro z _
    obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (pCore p J) z
    have hJrange : J ≤ (f.range.comap q).map J.subtype := by
      apply sup_le
      · intro h hh
        refine ⟨⟨h,hJ hh⟩, ?_, rfl⟩
        exact ⟨(QuotientGroup.mk' (pCore p H) ⟨h,hh⟩,1), by simp [f,l,r,q]; rfl⟩
      · intro a ha
        refine ⟨⟨a,aJ ha⟩, ?_, rfl⟩
        exact ⟨(1,⟨a,ha⟩), by simp [f,l,r,q]; rfl⟩
    obtain ⟨j',hj',he⟩ := hJrange j.property
    exact (Subtype.ext he : j' = j) ▸ hj'
  exact ⟨MulEquiv.ofBijective f ⟨hinj,hsurj⟩, fun h a => by
    change l (QuotientGroup.mk' (pCore p H) h) * r a = _
    rw [QuotientGroup.map_mk']
    exact (map_mul q _ _).symm⟩
/-- With an odd complement, every element whose square lies in the two-core
already lies in the Sylow overgroup. No order-two lift is required. -/
theorem mem_left_of_square_mem_join_twoCore {T : Sylow 2 G} {H A : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hAH : A ≤ normalizer (H : Set G))
    (hd : Disjoint H A) (hodd : Odd (Nat.card A))
    (hc : (A.subgroupOf (H ⊔ A)).map (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))) ≤
      center ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)))
    {y : G} (hy : y ∈ H ⊔ A) (hy2 : y ^ 2 ∈ (H ⊔ A).pCoreIn 2) : y ∈ H := by
  obtain ⟨e, he⟩ := exists_pCoreQuotient_product_of_sylow_le hTH hAH hd hc
  let J := H ⊔ A
  let q := QuotientGroup.mk' (pCore 2 J)
  let yJ : J := ⟨y,hy⟩
  have hy2' : yJ ^ 2 ∈ pCore 2 J := by
    obtain ⟨z,hz,heq⟩ := hy2
    exact (Subtype.ext heq : z = yJ ^ 2) ▸ hz
  have hq : (q yJ) ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hy2'
  have he2 : (e.symm (q yJ)).2 ^ 2 = 1 := by
    let r := (MonoidHom.snd (H ⧸ pCore 2 H) A).comp e.symm.toMonoidHom
    change (r (q yJ)) ^ 2 = 1
    rw [← map_pow, hq, map_one]
  have ha : (e.symm (q yJ)).2 = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right
      (_root_.orderOf_dvd_natCard _) (orderOf_dvd_of_pow_eq_one he2))
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (pCore 2 H) (e.symm (q yJ)).1
  have hcoord : e.symm (q yJ) = (QuotientGroup.mk' (pCore 2 H) x, 1) :=
    Prod.ext hx.symm ha
  have hqy : q yJ = q (inclusion le_sup_left x) := by
    rw [← e.apply_symm_apply (q yJ), hcoord, he]
    simp only [Subgroup.coe_one, mul_one]
    rfl
  have hyx : y / (x : G) ∈ H.pCoreIn 2 := by
    rw [← pCoreIn_sup_eq_of_sylow_le hTH hAH]
    exact mem_map_of_mem J.subtype (QuotientGroup.eq_iff_div_mem.mp hqy)
  simpa only [div_mul_cancel] using H.mul_mem ((pCoreIn_le 2 H) hyx) x.property
end Subgroup
