module

public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.PGroupCore

/-!
# Lifting invariant cubic Sylow overgroups through a two-core quotient

The intersection of an ambient Sylow subgroup T with a T-normalized subgroup
K is Sylow in K. Suppose a specified family of automorphisms of K/O₂(K)
contains the actual T-action, and its invariant index-three Sylow overgroups
generate the quotient. Their preimages are T-invariant; adjoining T preserves
index three. Thus these ambient cubic overgroups detect all of K.

The proof uses the literal quotient map and requires only relative normality.
Its consumer is the binary-linear terminal construction in Aschbacher--Smith
12.9.1, printed p.863 of `refs/quasithin.pdf`.
-/

public section
open Subgroup
namespace Subgroup.CubicSylowExtension
variable {G Q : Type*} [Group G] [Group Q] [Finite G]

/-- Invariant cubic generation in the quotient detects the normalized lift. -/
theorem le_of_cubic_overgroups (T : Sylow 2 G) (K M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* Q)
    (A : Subgroup (MulAut Q))
    (hTA : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      MulAut.congr eK ((pCore 2 K).quotientAut
        (K.normalizerMonoidHom ⟨t,hn ht⟩)) ∈ A)
    (generation : ∀ (S : Sylow 2 Q) (N : Subgroup Q),
      (S : Subgroup Q) ≤ N →
      (∀ J : Subgroup Q, (S : Subgroup Q) ≤ J → (S : Subgroup Q).relIndex J = 3 →
        (∀ a ∈ A, (S : Subgroup Q).map a.toMonoidHom = S → J.map a.toMonoidHom = J) →
          J ≤ N) → N = ⊤)
    (hlocal : ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y →
      Y ≤ K ⊔ (T : Subgroup G) → (T : Subgroup G).relIndex Y = 3 → Y ≤ M) :
    K ≤ M := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 K := by
    ext k
    change eK (QuotientGroup.mk k) = 1 ↔ k ∈ pCore 2 K
    rw [eK.map_eq_one_iff,QuotientGroup.eq_one_iff]
  have hkerP : q.ker ≤ (P : Subgroup K) := hker ▸ pCore_isPGroup.le_sylow_of_normal P
  let N := M.subgroupOf K
  have hPN : (P : Subgroup K) ≤ N := by
    rw [hP]
    exact fun _ hx => hTM hx
  have hkerN : q.ker ≤ N := hkerP.trans hPN
  let Pq := P.mapSurjective hq
  have hgen : N.map q = ⊤ := by
    apply generation Pq
    · exact map_mono hPN
    · intro J hPJ hi hinv
      let Jpre := J.comap q
      let Jamb := Jpre.map K.subtype
      let Y := Jamb ⊔ (T : Subgroup G)
      have hPJpre : (P : Subgroup K) ≤ Jpre := (map_le_iff_le_comap).mp hPJ
      have hnorm : (T : Subgroup G) ≤ normalizer (Jamb : Set G) := by
        intro t ht
        let a := K.normalizerMonoidHom ⟨t,hn ht⟩
        let b := (MulAut.congr eK) ((pCore 2 K).quotientAut a)
        have he (k : K) : b (q k) = q (a k) := by
          dsimp only [b,q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
          simp only [MulAut.congr_apply, MulEquiv.trans_apply, eK.symm_apply_apply,quotientAut_apply_mk]
        have hehom : b.toMonoidHom.comp q = q.comp a.toMonoidHom :=
          MonoidHom.ext he
        have haP : (P : Subgroup K).map a.toMonoidHom = P := by
          rw [hP]
          ext x
          constructor
          · rintro ⟨y,hy,rfl⟩
            change (a y : K).val ∈ (T : Subgroup G)
            rw [normalizerMonoidHom_apply_apply_coe]
            exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hy)
              ((T : Subgroup G).inv_mem ht)
          · intro hx
            refine ⟨a.symm x,?_,a.apply_symm_apply x⟩
            change (a.symm x : K).val ∈ (T : Subgroup G)
            have he : a.symm = K.normalizerMonoidHom ⟨t⁻¹,(normalizer (K : Set G)).inv_mem (hn ht)⟩ :=
              (map_inv K.normalizerMonoidHom ⟨t,hn ht⟩).symm
            rw [he,normalizerMonoidHom_apply_apply_coe,inv_inv]
            exact (T : Subgroup G).mul_mem
              ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem ht) hx) ht
        have hbP : (Pq : Subgroup (Q)).map b.toMonoidHom = Pq := by
          change ((P : Subgroup K).map q).map b.toMonoidHom = (P : Subgroup K).map q
          rw [map_map,hehom,←map_map,haP]
        have hbJ := hinv b (hTA t ht) hbP
        have haJ : Jpre.map a.toMonoidHom = Jpre := by
          apply le_antisymm
          · rintro k ⟨l,hl,rfl⟩
            change q (a l) ∈ J
            rw [←he]
            exact hbJ ▸ mem_map_of_mem b.toMonoidHom hl
          · intro k hk
            refine ⟨a.symm k,?_,a.apply_symm_apply k⟩
            change q (a.symm k) ∈ J
            have hm : b (q (a.symm k)) ∈ J := by rwa [he,a.apply_symm_apply]
            have hcom : J.comap b.toMonoidHom = J := by
              have hh := congrArg (Subgroup.comap b.toMonoidHom) hbJ
              simpa only [comap_map_eq, (b.toMonoidHom.ker_eq_bot b.injective), sup_bot_eq] using hh.symm
            exact hcom ▸ hm
        apply mem_normalizer_iff_map_conj_eq.mpr
        change (Jpre.map K.subtype).map (MulAut.conj t).toMonoidHom = Jpre.map K.subtype
        have hc : (MulAut.conj t).toMonoidHom.comp K.subtype = K.subtype.comp a.toMonoidHom := by
          apply MonoidHom.ext
          intro k
          exact (normalizerMonoidHom_apply_apply_coe K ⟨t,hn ht⟩ k).symm
        rw [map_map,hc,←map_map,haJ]
      have hkerJ : q.ker ≤ Jpre := hkerP.trans hPJpre
      have hpreIndex : (P : Subgroup K).relIndex Jpre = 3 := by
        have hh := relIndex_map_map q (P : Subgroup K) Jpre
        rw [sup_eq_left.mpr hkerP,sup_eq_left.mpr hkerJ,
          map_comap_eq_self_of_surjective hq] at hh
        exact hh.symm.trans hi
      have hYindex : (T : Subgroup G).relIndex Y = 3 := by
        rw [show Y = Jamb ⊔ (T : Subgroup G) from rfl,
          relIndex_sup_of_normalizes_left Jamb (T : Subgroup G) hnorm]
        have hh := relIndex_comap (T : Subgroup G) K.subtype Jpre
        change ((T : Subgroup G).subgroupOf K).relIndex Jpre =
          (T : Subgroup G).relIndex Jamb at hh
        rw [←hP] at hh
        exact hh.symm.trans hpreIndex
      have hYM := hlocal Y le_sup_right
        (sup_le_sup (map_subtype_le Jpre) le_rfl) hYindex
      have hpreN : Jpre ≤ N := (map_le_iff_le_comap).mp (le_sup_left.trans hYM)
      have hh := map_mono (f := q) hpreN
      rwa [map_comap_eq_self_of_surjective hq] at hh
  have hN : N = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hgen
    rwa [comap_map_eq,sup_eq_left.mpr hkerN,comap_top] at hh
  intro k hk
  exact show (⟨k,hk⟩ : K) ∈ N from hN ▸ mem_top _
/-- Extract an actual cubic Sylow overgroup escaping the specified subgroup. -/
theorem exists_cubic_overgroup (T : Sylow 2 G) (K M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* Q)
    (A : Subgroup (MulAut Q))
    (hTA : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      MulAut.congr eK ((pCore 2 K).quotientAut
        (K.normalizerMonoidHom ⟨t,hn ht⟩)) ∈ A)
    (generation : ∀ (S : Sylow 2 Q) (N : Subgroup Q),
      (S : Subgroup Q) ≤ N →
      (∀ J : Subgroup Q, (S : Subgroup Q) ≤ J → (S : Subgroup Q).relIndex J = 3 →
        (∀ a ∈ A, (S : Subgroup Q).map a.toMonoidHom = S → J.map a.toMonoidHom = J) →
          J ≤ N) → N = ⊤) (hKM : ¬ K ≤ M) :
    ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧ H ≤ K ⊔ (T : Subgroup G) ∧
      (T : Subgroup G).relIndex H = 3 ∧ ¬ H ≤ M := by
  by_contra! hall
  exact hKM (le_of_cubic_overgroups T K M hTM hn eK A hTA generation hall)
end Subgroup.CubicSylowExtension
