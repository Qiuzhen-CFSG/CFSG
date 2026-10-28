module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSetup
public import Theory.GroupTheory.TwoCoatomInterchange
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Source Borel identification from two maximal local overgroups

The component Sylow normalizer is invariant under its Sylow stabilizer;
its join with S has characteristic two and lies in M by 2.5.1. Both full
parabolics cannot be invariant, as their characteristic-two joins would
then generate the component inside M. The two-coatom geometry therefore
produces an interchange and forces the invariant intersection M∩D to be
the Borel. Components may be permuted by S and central covers are retained.

Source: Aschbacher--Smith 2.5.2(2), printed p.551. Only intrinsic rank-two
geometry is explicit here; the following model applications discharge it.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

private theorem intersection_invariant {J : Type*} [Group J]
    (A D : Subgroup J) (s : normalizer (D : Set J)) (hs : (s : J) ∈ A) :
    (A.subgroupOf D).map (D.normalizerMonoidHom s).toMonoidHom = A.subgroupOf D := by
  have hf (u : normalizer (D : Set J)) (hu : (u : J) ∈ A) {x : D}
      (hx : x ∈ A.subgroupOf D) : D.normalizerMonoidHom u x ∈ A.subgroupOf D := by
    change (D.normalizerMonoidHom u x : J) ∈ A
    rw [normalizerMonoidHom_apply_apply_coe]
    exact A.mul_mem (A.mul_mem hu hx) (A.inv_mem hu)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hf s hs hy
  · intro hx
    refine ⟨D.normalizerMonoidHom s⁻¹ x, hf s⁻¹ (A.inv_mem hs) hx, ?_⟩
    rw [map_inv]
    exact (D.normalizerMonoidHom s).apply_symm_apply x

/-- Exact 2.5.2(2) intersection and interchange from intrinsic two-parabolic
geometry; no normalizer-placement or diagram-action hypothesis is assumed. -/
theorem rank_two_intersection_eq_borel_source
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (D : Subgroup H) (hD : IsComponent H D) (hout : ¬ D.map H.subtype ≤ M)
    (B P Q : Subgroup D)
    (hB : B = normalizer ((S : Subgroup H).subgroupOf D : Set D))
    (hBc : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (hPc : centralizer (pCore 2 P : Set P) ≤ pCore 2 P)
    (hQc : centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q)
    (hP : IsCoatom P) (hQ : IsCoatom Q) (hPQ : P ≠ Q)
    (hinf : P ⊓ Q = B) (hsup : P ⊔ Q = ⊤)
    (hcover : ∀ J : Subgroup D, B ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q) :
    ((M.subgroupOf H).subgroupOf D) = B ∧
      ∃ s : normalizer (D : Set H), (s : H) ∈ S ∧
        P.map (D.normalizerMonoidHom s).toMonoidHom = Q ∧
        Q.map (D.normalizerMonoidHom s).toMonoidHom = P := by
  let A : Set (MulAut D) := {a | ∃ s : normalizer (D : Set H),
    (s : H) ∈ S ∧ D.normalizerMonoidHom s = a}
  let I := (M.subgroupOf H).subgroupOf D
  have hI : I ≠ ⊤ := by
    intro he
    apply hout
    rintro x ⟨d, hd, rfl⟩
    exact (show (⟨d,hd⟩ : D) ∈ I from he ▸ mem_top _)
  have hAB : ∀ a ∈ A, B.map a.toMonoidHom = B := by
    rintro a ⟨s, hs, rfl⟩
    rw [hB, map_equiv_normalizer_eq, intersection_invariant (S : Subgroup H) D s hs]
  have hAI : ∀ a ∈ A, I.map a.toMonoidHom = I := by
    rintro a ⟨s, hs, rfl⟩
    exact intersection_invariant (M.subgroupOf H) D s
      (hSM (mem_map_of_mem H.subtype hs))
  have hforce (K : Subgroup D)
      (hc : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
      (hinv : ∀ a ∈ A, K.map a.toMonoidHom = K) : K ≤ I := by
    let KH := K.map D.subtype
    let XH := KH ⊔ (S : Subgroup H)
    let X := XH.map H.subtype
    have hn : (S : Subgroup H) ⊓ normalizer (D : Set H) ≤ normalizer (KH : Set H) := by
      intro s hs
      apply mem_normalizer_iff_map_conj_eq.mpr
      let a := D.normalizerMonoidHom ⟨s,hs.2⟩
      have ha := hinv a ⟨⟨s,hs.2⟩,hs.1,rfl⟩
      change (K.map D.subtype).map (MulAut.conj s).toMonoidHom = K.map D.subtype
      have hh : (MulAut.conj s).toMonoidHom.comp D.subtype = D.subtype.comp a.toMonoidHom := by
        ext x; rfl
      rw [map_map, hh, ← map_map, ha]
    have hKH : KH ⊓ centralizer (KH.pCoreIn 2 : Set H) ≤ KH.pCoreIn 2 := by
      exact (inf_centralizer_pCoreIn_le_iff 2 KH).mpr
        ((Theory.Quasithin.centralizer_pCore_le_iff 2
          (K.equivMapOfInjective D.subtype D.subtype_injective)).mp hc)
    have hXH := hD.local_adjoin_centralizer (map_subtype_le K) S.isPGroup' hn hKH
    have hXe : X ∈ Chapter1.He G := by
      apply Chapter1.mem_He_iff.mpr
      exact (Theory.Quasithin.centralizer_pCore_le_iff 2
        (XH.equivMapOfInjective H.subtype H.subtype_injective)).mp
          ((inf_centralizer_pCoreIn_le_iff 2 XH).mp hXH)
    have hSX : (S : Subgroup H).map H.subtype ≤ X := map_mono le_sup_right
    have hXcore : twoCore X ≠ ⊥ := by
      intro hb
      have hXB : X = ⊥ := by
        apply bot_unique
        intro x hx
        have hec : X ⊓ centralizer (twoCore X : Set G) ≤ twoCore X := hXe
        rw [hb] at hec
        apply hec
        refine ⟨hx, ?_⟩
        intro y hy
        rw [show y = 1 from hy]
        simp
      have hcoreH := (hH.elim (fun h => h.1.1) (fun h => h.1)).1
      apply hcoreH
      apply bot_unique
      rw [← hXB]
      exact (pCoreIn_le_sylow H S).trans hSX
    obtain ⟨R, hR⟩ := sylow_image_in_inf S hSM
    have hXM : X ≤ M := heOver_le_of_empty hH hempty R
      (hR.symm ▸ (show X ∈ Chapter1.HeOver G
        ((S : Subgroup H).map H.subtype : Set G) from ⟨hXe,hXcore,hSX⟩))
    intro d hd
    exact hXM (mem_map_of_mem H.subtype (mem_sup_left (mem_map_of_mem D.subtype hd)))
  have hBI : B ≤ I := hforce B hBc hAB
  have hnon : ¬ ∀ a ∈ A, P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q := by
    intro hall
    have hp := hforce P hPc (fun a ha => (hall a ha).1)
    have hq := hforce Q hQc (fun a ha => (hall a ha).2)
    apply hI
    apply top_unique
    rw [← hsup]
    exact sup_le hp hq
  obtain ⟨he, a, ha, hp, hq⟩ := eq_inf_and_exists_interchange_of_two_coatoms
    B P Q I hP hQ hPQ hinf hcover A hAB hAI hnon hBI hI
  obtain ⟨s, hs, rfl⟩ := ha
  exact ⟨he,s,hs,hp,hq⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
