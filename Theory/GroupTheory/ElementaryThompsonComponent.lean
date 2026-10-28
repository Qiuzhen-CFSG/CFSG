module

public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.GroupTheory.CComponent.CommutatorDichotomy
public import Theory.GroupTheory.Commutator.NormalizesSupplement

/-!
# Thompson commutators from characteristic-normalizer control

Let a normal C-component K supplement a Sylow two-subgroup S. If
O∞(K) N_K(J(S)) is proper in K, then K = [K,J(S)].

The C-component dichotomy reduces the proof to [K,J(S)] ≤ O∞(G).
Its intersection with K lies in the intrinsic radical of K. Consequently
D = J(S) O∞(K) is normal in G = KS. The Sylow intersection S ∩ D has
Thompson subgroup J(S), so Frattini gives G = N_G(J(S)) D. Absorbing
J(S) into its normalizer and intersecting with K gives the forbidden
K = O∞(K) N_K(J(S)). This does not require J(S) ≤ O∞(K).

The module also proves nontriviality of the elementary Thompson subgroup
of a nontrivial finite two-group. All radicals of subgroups are explicitly
mapped through their subtype homomorphisms.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.6.16(3), printed p.930; Proposition A.3.3(7), printed pp.42–43.
-/

public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem maxJ_normalizer (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change S.map (MulAut.conj g).toMonoidHom = S at hg
  change (elementaryAbelianMaxJ S).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv, hg]

/-- The actual elementary Thompson subgroup of a nontrivial finite
 two-group is nontrivial. -/
theorem elementaryAbelianMaxJ_top_ne_bot_of_isPGroup (hp : IsPGroup 2 G) [Nontrivial G] :
    elementaryAbelianMaxJ (⊤ : Subgroup G) ≠ ⊥ := by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hd : 2 ∣ Nat.card G := (hp.dvd_orderOf hg).trans (orderOf_dvd_natCard g)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 hd
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty (⊤ : Subgroup G)
  have hc := hA.2.2 (zpowers a) le_top
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← ha]; exact pow_orderOf_eq_one a))
  intro hbot
  have hAbot : A = ⊥ := bot_unique ((le_sSup hA).trans hbot.le)
  rw [hAbot, Nat.card_zpowers, ha, Subgroup.card_bot] at hc
  omega

/-- Frattini generation for any normal subgroup containing J(S). -/
theorem elementaryAbelianMaxJ_frattini_of_le_normal (S : Sylow 2 G) (D : Subgroup G) [D.Normal]
    (hJD : elementaryAbelianMaxJ (S : Subgroup G) ≤ D) :
    normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G) ⊔ D = ⊤ := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal D
  let Q := (P : Subgroup D).map D.subtype
  have hQ : Q = (S : Subgroup G) ⊓ D := by
    rw [show Q = (P : Subgroup D).map D.subtype from rfl, hP, subgroupOf_map_subtype]
  have hJQ : elementaryAbelianMaxJ Q = elementaryAbelianMaxJ (S : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate _ _
      (hQ ▸ le_inf (sSup_le fun _ hA => hA.1) hJD) (hQ ▸ inf_le_left)
  have hn : normalizer (Q : Set G) ≤
      normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G) := by
    rw [← hJQ]
    exact maxJ_normalizer Q
  exact top_unique (P.normalizer_sup_eq_top.symm.le.trans (sup_le_sup_right hn D))

private theorem inf_radical_le (K : Subgroup G) :
    K ⊓ solvableRadical G ≤ (solvableRadical K).map K.subtype := by
  let f := K.subtype.subgroupComap (solvableRadical G)
  let : Group.IsSolvable ((solvableRadical G).subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective (f := f)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun r : solvableRadical G => (r : G)) h)))
  have h := le_solvableRadical ((solvableRadical G).subgroupOf K) inferInstance inferInstance
  rintro x ⟨hxK, hxR⟩
  exact ⟨⟨x, hxK⟩, h hxR, rfl⟩

/-- The radical branch gives the required generation inside K, using
 the intrinsic radical of K rather than the ambient radical. -/
theorem radical_sup_normalizer_maxJ_eq_of_commutator_le (S : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hgen : K ⊔ (S : Subgroup G) = ⊤)
    (hcomm : ⁅K, elementaryAbelianMaxJ (S : Subgroup G)⁆ ≤ solvableRadical G) :
    (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G)) = K := by
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let R := (solvableRadical K).map K.subtype
  let D := J ⊔ R
  let N := normalizer (J : Set G)
  have hR : R ≤ K := map_subtype_le _
  have hSN : (S : Subgroup G) ≤ N := (S : Subgroup G).le_normalizer.trans (maxJ_normalizer _)
  have hc : ⁅K, J⁆ ≤ R := (le_inf (commutator_le_left K J) hcomm).trans (inf_radical_le K)
  let : R.Normal := inferInstance
  let : D.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    refine sup_le ?_ ?_
    · apply le_normalizer_sup_of_commutator_le J K J R le_rfl
      rwa [commutator_comm]
    · exact hSN.trans normalizer_le_normalizer_sup_normal
  have hFr : N ⊔ D = ⊤ := elementaryAbelianMaxJ_frattini_of_le_normal S D le_sup_left
  have hNR : N ⊔ R = ⊤ := by
    change N ⊔ (J ⊔ R) = ⊤ at hFr
    rw [← sup_assoc, sup_of_le_left (show J ≤ N from J.le_normalizer)] at hFr
    exact hFr
  apply le_antisymm (sup_le hR inf_le_left)
  intro k hk
  obtain ⟨n, hn, r, hr, he⟩ := mem_sup_of_normal_right.mp
    (hNR.symm ▸ mem_top k)
  have hnK : n ∈ K := by
    have hh := K.mul_mem hk (K.inv_mem (hR hr))
    rw [← he, mul_inv_cancel_right] at hh
    exact hh
  rw [← he]
  exact (R ⊔ (K ⊓ N)).mul_mem (show n ∈ R ⊔ (K ⊓ N) from mem_sup_right ⟨hnK, hn⟩)
    (show r ∈ R ⊔ (K ⊓ N) from mem_sup_left hr)

/-- A normal C-component with proper radical–Thompson-normalizer product
 is generated by its commutators with the elementary Thompson subgroup. -/
theorem eq_commutator_maxJ_of_radical_normalizer_lt (S : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hK : K.IsCComponent) (hgen : K ⊔ (S : Subgroup G) = ⊤)
    (hstrict : (solvableRadical K).map K.subtype ⊔
      (K ⊓ normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G)) < K) :
    K = ⁅K, elementaryAbelianMaxJ (S : Subgroup G)⁆ := by
  rcases hK.commutator_le_radical_or_eq_iSup_conjugates
    (elementaryAbelianMaxJ (S : Subgroup G)) with hc | hc
  · exact False.elim (hstrict.ne (radical_sup_normalizer_maxJ_eq_of_commutator_le S K hgen hc))
  · apply le_antisymm ?_ (commutator_le_left _ _)
    rw [hc]
    exact le_iSup_conjugates _ _

end Stellmacher
end
