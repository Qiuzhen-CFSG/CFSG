module

public import Theory.GroupTheory.PStar.ExtensionCentralSylow
public import Theory.GroupTheory.ChiefFactorDirectPower
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowCommutingJoin
public import Theory.GroupTheory.SylowNormalSupplementProduct

/-!
# P-star extensions across a chief kernel

For a normal subgroup M, chief minimality gives either M intersect N = 1
or N contained in M. The disjoint branch lifts quotient centralizers:
commutators lie in both normal subgroups and hence vanish.

For the containment branch, let X be the embedded p-residual of C_G(P).
The central-Sylow kernel theorem makes X p-star and p-perfectness gives
G = NX. Consequently M = N(M intersect X). A chosen Sylow Q₀ of
M intersect X commutes with P, and the normal-supplement index calculation
makes PQ₀ Sylow in M. The p-star supplement inside X centralizes this
actual product. Sylow conjugacy then gives the required supplement for
every supplied Sylow subgroup of M.

Source: GLS II, Chapter B, Lemma 5.3, chief-kernel argument
(`refs/KGroup/GLS2/ChapterB.tex`, lines 619–621). The separately proved
central-Sylow kernel result removes the source's induction on C_G(P).
-/

public section

open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory
variable {p : ℕ} {G : Type*} [Group G] [Finite G] [Fact p.Prime]

theorem IsPStar.supplement_sylow_conjugate (M : Subgroup G) [M.Normal]
    (P Q : Sylow p M)
    (hP : M ⊔ centralizer ((P : Subgroup M).map M.subtype : Set G) = ⊤) :
    M ⊔ centralizer ((Q : Subgroup M).map M.subtype : Set G) = ⊤ := by
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M P Q
  let e := MulAut.conj (m : G)
  have he : M.subtype.comp (MulAut.conj m).toMonoidHom =
      e.toMonoidHom.comp M.subtype := by ext x; rfl
  have hPQ := congrArg (fun S : Sylow p M => (S : Subgroup M).map M.subtype) hm
  have hm' : MulAut.conj m • (P : Subgroup M) = (Q : Subgroup M) := by
    exact congrArg (fun R : Sylow p M => (R : Subgroup M)) hm
  have hPQ' : ((P : Subgroup M).map M.subtype).map e.toMonoidHom =
      (Q : Subgroup M).map M.subtype := by
    rw [map_map, ← he, ← map_map]
    change map M.subtype (MulAut.conj m • (P : Subgroup M)) = _
    rw [hm']
  have hPQ := hPQ'
  have h := congrArg (Subgroup.map e.toMonoidHom) hP
  rw [Subgroup.map_sup, map_top_of_surjective _ e.surjective] at h
  apply top_unique
  rw [← h]
  apply sup_le_sup
  · rintro _ ⟨x, hx, rfl⟩
    exact (inferInstance : M.Normal).conj_mem x hx m
  · have hc := map_centralizer_le_centralizer_image
      ((P : Subgroup M).map M.subtype : Set G) e.toMonoidHom
    simpa only [← coe_map, hPQ] using hc

theorem IsPStar.supplement_of_disjoint (N M : Subgroup G) [N.Normal] [M.Normal]
    (hNM : M ⊓ N = ⊥) (hquot : IsPStar p (G ⧸ N)) (Q : Sylow p M) :
    M ⊔ centralizer ((Q : Subgroup M).map M.subtype : Set G) = ⊤ := by
  let S := (Q : Subgroup M).map M.subtype
  let q := QuotientGroup.mk' N
  let C := centralizer (S : Set G)
  have hlift : (centralizer (S.map q : Set (G ⧸ N))).comap q ≤ C := by
    intro x hx y hy
    have hyM : y ∈ M := map_subtype_le _ hy
    have hcommN : ⁅x, y⁆ ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q ⁅x, y⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (hx (q y) (mem_map_of_mem q hy)).symm
    have hcommM : ⁅x, y⁆ ∈ M := by
      exact M.mul_mem ((inferInstance : M.Normal).conj_mem y hyM x) (M.inv_mem hyM)
    have hone : ⁅x, y⁆ = 1 := by
      exact mem_bot.mp (hNM.le ⟨hcommM, hcommN⟩)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  have hC : centralizer (S.map q : Set (G ⧸ N)) ≤ C.map q := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact mem_map_of_mem q (hlift hx)
  have hgen := hquot.sup_image_centralizer_eq_top q (QuotientGroup.mk'_surjective N) M Q
  have hcover : (M ⊔ C).map q = ⊤ := by
    apply top_unique
    rw [Subgroup.map_sup, ← hgen]
    exact sup_le_sup_left hC _
  have hNC : N ≤ C := by
    apply (commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_disjoint (disjoint_iff.mpr (inf_comm N M ▸ hNM)))).trans
    exact centralizer_le (map_subtype_le _)
  have h := congrArg (Subgroup.comap q) hcover
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk',
    sup_eq_left.mpr (hNC.trans le_sup_right), comap_top] using h

/-- The containment branch: a p-star supplement centralizing P supplies
centralizer supplements for every normal subgroup containing N. -/
theorem IsPStar.supplement_of_normal_le
    (N M X : Subgroup G) [N.Normal] [M.Normal]
    (P : Sylow p N) (hX : IsPStar p X)
    (hcover : N ⊔ X = ⊤)
    (hXC : X ≤ centralizer ((P : Subgroup N).map N.subtype : Set G))
    (hNM : N ≤ M) (Q : Sylow p M) :
    M ⊔ centralizer ((Q : Subgroup M).map M.subtype : Set G) = ⊤ := by
  let D := M.subgroupOf X
  let D' := D.map X.subtype
  let Q0 : Sylow p D := Sylow.nonempty.some
  let e := D.equivMapOfInjective X.subtype X.subtype_injective
  let Q1 : Sylow p D' := Q0.mapSurjective (f := e.toMonoidHom) e.surjective
  let U := (P : Subgroup N).map N.subtype
  let V := (Q1 : Subgroup D').map D'.subtype
  let T := U ⊔ V
  have hV : V = ((Q0 : Subgroup D).map D.subtype).map X.subtype := by
    change ((Q0 : Subgroup D).map e.toMonoidHom).map D'.subtype = _
    rw [map_map, map_map]
    rfl
  have hDX : D' ≤ X := map_subtype_le _
  have hDM : D' ≤ M := by
    rw [show D' = M ⊓ X from subgroupOf_map_subtype M X]
    exact inf_le_left
  have hgenM : N ⊔ D' = M := by
    apply le_antisymm (sup_le hNM hDM)
    intro m hm
    have ht : m ∈ N ⊔ X := hcover.ge (mem_top m)
    obtain ⟨n, hn, x, hx, hnx⟩ := mem_sup_of_normal_left.mp ht
    have hxM : x ∈ M := by
      have hh := M.mul_mem (M.inv_mem (hNM hn)) hm
      rwa [← hnx, inv_mul_cancel_left] at hh
    rw [← hnx]
    apply (N ⊔ D').mul_mem ((le_sup_left : N ≤ N ⊔ D') hn)
    apply (le_sup_right : D' ≤ N ⊔ D')
    exact mem_map.mpr ⟨⟨x, hx⟩, hxM, rfl⟩
  have hVp : IsPGroup p V := Q1.isPGroup'.map D'.subtype
  have hVN : V ≤ normalizer (U : Set G) :=
    ((map_subtype_le _).trans (hDX.trans hXC)).trans (centralizer_le_normalizer _)
  have hTp : IsPGroup p T := (P.isPGroup'.map N.subtype).to_sup_of_normal_left' hVp hVN
  have hTle : T ≤ N ⊔ D' := sup_le_sup (map_subtype_le _) (map_subtype_le _)
  obtain ⟨S, hS⟩ := hTp.exists_sylow_sup_of_normal_sylow_images N D' T hTle
    P Q1 le_sup_left le_sup_right
  let eM := MulEquiv.subgroupCongr hgenM
  let S' : Sylow p M := S.mapSurjective (f := eM.toMonoidHom) eM.surjective
  have hS' : (S' : Subgroup M).map M.subtype = T := by
    change ((S : Subgroup (N ⊔ D' : Subgroup G)).map eM.toMonoidHom).map M.subtype = T
    rw [map_map]
    exact hS
  let C0 := centralizer ((Q0 : Subgroup D).map D.subtype : Set X)
  have hC0 : C0.map X.subtype ≤ centralizer (T : Set G) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact (le_centralizer_iff.mp hXC).trans (centralizer_le (map_subtype_le _))
    · apply le_centralizer_iff.mp
      have h := map_centralizer_le_centralizer_image
        ((Q0 : Subgroup D).map D.subtype : Set X) X.subtype
      simpa only [← coe_map, ← hV] using h
  have hXC' : X ≤ M ⊔ centralizer (T : Set G) := by
    have h := congrArg (Subgroup.map X.subtype) (hX.2 D Q0)
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at h
    rw [← h]
    exact sup_le (hDM.trans le_sup_left) (hC0.trans le_sup_right)
  have hSgen : M ⊔ centralizer ((S' : Subgroup M).map M.subtype : Set G) = ⊤ := by
    rw [hS']
    apply top_unique
    rw [← hcover]
    exact sup_le (hNM.trans le_sup_left) hXC'
  exact IsPStar.supplement_sylow_conjugate M S' Q hSgen

/-- GLS II B.5.3 for a chief kernel, with its Sylow-centralizer supplement. -/
theorem isPStar_of_isChief_centralizer_supplement
    (hG : IsPPerfect p G) (N : Subgroup G) [N.Normal]
    (hN : ChiefFactor.IsChief N ⊥) (P : Sylow p N)
    (hquot : IsPStar p (G ⧸ N))
    (hgen : N ⊔ centralizer ((P : Subgroup N).map N.subtype : Set G) = ⊤) :
    IsPStar p G := by
  let C := centralizer ((P : Subgroup N).map N.subtype : Set G)
  let R := pResidual p C
  let X := R.map C.subtype
  have hR : IsPStar p R := isPStar_pResidual_centralizer_of_quotient N P hquot hgen
  have hX : IsPStar p X := hR.of_equiv (R.equivMapOfInjective C.subtype C.subtype_injective)
  have hcover : N ⊔ X = ⊤ := sup_embedded_pResidual_eq_top hG N C hgen
  refine ⟨(pResidual_eq_top_iff p G).mpr hG, ?_⟩
  intro M hM Q
  rcases hN.minimal (M ⊓ N) inferInstance bot_le inf_le_right with hdisj | hcontain
  · exact IsPStar.supplement_of_disjoint N M hdisj hquot Q
  · exact IsPStar.supplement_of_normal_le N M X P hX hcover (map_subtype_le _)
      (hcontain ▸ (inf_le_left : M ⊓ N ≤ M)) Q

end Theory.GroupTheory
