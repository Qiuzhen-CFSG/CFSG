module

public import Theory.GroupTheory.PGroup.NormalizerBarrier
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group

/-!
# Local control from one unique fixed coset

If an element z of M fixes exactly one coset of M, any transporter taking z
back into M lies in M. The normalizer condition in a finite p-group then
places every p-subgroup containing z, and its ambient normalizer, in M.
If z is central in a Sylow p-subgroup T contained in M, M controls fusion
of all p-elements of M. The proof conjugates a copy of z inside the
centralizer of the target element and applies the transporter bound.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Proposition 2.2.2, pp. 519–520, including (*).
The canonical left coset action corresponds to the source's right coset
action by inversion. No strong-embedding or recognition premise is used.
-/

open Subgroup
namespace UniqueFixedCoset
variable {G : Type*} [Group G]

public theorem fixed_iff (M : Subgroup G) (x g : G) :
    x • (QuotientGroup.mk g : G ⧸ M) = QuotientGroup.mk g ↔ g⁻¹ * x * g ∈ M := by
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
  simpa only [smul_eq_mul, mul_inv_rev, inv_inv, mul_assoc] using
    (M.inv_mem_iff (x := g⁻¹ * x * g))

public theorem transporter_mem {M : Subgroup G} {x g : G} (hxM : x ∈ M)
    (hunique : ∃! q : G ⧸ M, x • q = q) (hg : g * x * g⁻¹ ∈ M) : g ∈ M := by
  have hbase : x • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := by
    simpa using (fixed_iff M x 1).mpr (by simpa using hxM)
  have hfix : x • (QuotientGroup.mk g⁻¹ : G ⧸ M) = QuotientGroup.mk g⁻¹ :=
    (fixed_iff M x g⁻¹).mpr (by simpa using hg)
  have he := hunique.unique hbase hfix
  have : g⁻¹ ∈ M := by simpa using QuotientGroup.eq.mp he
  exact M.inv_mem_iff.mp this

public theorem unique_of_fusion_and_centralizer {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hC : centralizer ({x} : Set G) ≤ M)
    (hfusion : ∀ g : G, g * x * g⁻¹ ∈ M →
      ∃ m ∈ M, g * x * g⁻¹ = m * x * m⁻¹) :
    ∃! q : G ⧸ M, x • q = q := by
  have htrans : ∀ g : G, g * x * g⁻¹ ∈ M → g ∈ M := by
    intro g hg
    obtain ⟨m, hm, he⟩ := hfusion g hg
    have hcg : m⁻¹ * g ∈ centralizer ({x} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      calc
        (m⁻¹ * g) * x * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * x * g⁻¹) * m := by group
        _ = x := by rw [he]; group
    simpa only [mul_inv_cancel_left] using M.mul_mem hm (hC hcg)
  refine ⟨QuotientGroup.mk 1, (fixed_iff M x 1).mpr (by simpa using hxM), ?_⟩
  intro q
  refine Quotient.inductionOn' q ?_
  intro g hg
  apply QuotientGroup.eq.mpr
  simpa using htrans g⁻¹ (by simpa using (fixed_iff M x g).mp hg)

public theorem normalizer_le {M S : Subgroup G} {z : G}
    (hzM : z ∈ M) (hunique : ∃! q : G ⧸ M, z • q = q)
    (hzS : z ∈ S) (hSM : S ≤ M) : normalizer (S : Set G) ≤ M := by
  intro g hg
  exact transporter_mem hzM hunique (hSM ((mem_normalizer_iff.mp hg z).mp hzS))

public theorem p_overgroup_and_normalizer_le {p : ℕ} [Fact p.Prime]
    {M S : Subgroup G} [Finite S] {z : G}
    (hzM : z ∈ M) (hunique : ∃! q : G ⧸ M, z • q = q)
    (hS : IsPGroup p S) (hzS : z ∈ S) :
    S ≤ M ∧ normalizer (S : Set G) ≤ M := by
  have hSM : S ≤ M := p_overgroup_le_of_normalizers_le hS
    (zpowers_le.mpr hzS) (zpowers_le.mpr hzM) (by
      intro W _ hZW hWM
      exact normalizer_le hzM hunique (hZW (mem_zpowers z)) hWM)
  exact ⟨hSM, normalizer_le hzM hunique hzS hSM⟩

private theorem exists_conj_mem_sylow [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {x : G} (hx : IsPGroup p (zpowers x)) :
    ∃ g : G, g * x * g⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  rw [← hg]
  exact ⟨x, hQ (mem_zpowers x), rfl⟩

public theorem sylow_fusion [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    {z : G} (hzT : z ∈ (T : Subgroup G))
    (hzcentral : ∀ t ∈ (T : Subgroup G), Commute z t)
    (hunique : ∃! q : G ⧸ M, z • q = q)
    {x y : G} (hx : x ∈ (T : Subgroup G)) (hy : y ∈ (T : Subgroup G))
    (hxy : IsConj x y) : ∃ m ∈ M, m * x * m⁻¹ = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  let C := centralizer ({y} : Set G)
  have hzC : z ∈ C := mem_centralizer_singleton_iff.mpr (hzcentral y hy).eq
  have hZp : IsPGroup p (zpowers z) := T.isPGroup'.of_injective
    (inclusion (zpowers_le.mpr hzT)) (inclusion_injective _)
  obtain ⟨P, hP⟩ := (hZp.comap_subtype (K := C)).exists_le_sylow
  have hzP : z ∈ (P : Subgroup C).map C.subtype :=
    ⟨⟨z, hzC⟩, hP (mem_zpowers z), rfl⟩
  have hPM : (P : Subgroup C).map C.subtype ≤ M :=
    (p_overgroup_and_normalizer_le (hTM hzT) hunique (P.isPGroup'.map C.subtype) hzP).1
  have hgzC : g * z * g⁻¹ ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj g) (hzcentral x hx).eq
    change (g * z * g⁻¹) * y = y * (g * z * g⁻¹)
    simpa only [map_mul, show MulAut.conj g x = y from hg, MulAut.conj_apply] using hh
  have hgZp : IsPGroup p (zpowers (⟨g * z * g⁻¹, hgzC⟩ : C)) := by
    have hp := hZp.map (MulAut.conj g).toMonoidHom
    have hle : zpowers (⟨g * z * g⁻¹, hgzC⟩ : C) ≤
        ((zpowers z).map (MulAut.conj g).toMonoidHom).subgroupOf C :=
      zpowers_le.mpr ⟨z, mem_zpowers z, rfl⟩
    exact (hp.comap_subtype (K := C)).of_injective (inclusion hle) (inclusion_injective hle)
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow P hgZp
  have hcgM : (c : G) * g ∈ M := by
    apply transporter_mem (hTM hzT) hunique
    have hh := hPM (mem_map.mpr ⟨_, hc, rfl⟩)
    change (c : G) * (g * z * g⁻¹) * (c : G)⁻¹ ∈ M at hh
    simpa only [mul_inv_rev, mul_assoc] using hh
  refine ⟨(c : G) * g, hcgM, ?_⟩
  calc
    (↑c * g) * x * (↑c * g)⁻¹ = ↑c * (g * x * g⁻¹) * (↑c)⁻¹ := by group
    _ = ↑c * y * (↑c)⁻¹ := by rw [hg]
    _ = y := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property)

public theorem p_element_conjugate_into_sylow [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    {x : G} (hxM : x ∈ M) (hx : IsPGroup p (zpowers x)) :
    ∃ m ∈ M, m * x * m⁻¹ ∈ (T : Subgroup G) := by
  have hp : IsPGroup p (zpowers (⟨x, hxM⟩ : M)) := by
    have hle : zpowers (⟨x, hxM⟩ : M) ≤ (zpowers x).subgroupOf M :=
      zpowers_le.mpr (mem_zpowers x)
    exact hx.comap_subtype.of_injective (inclusion hle) (inclusion_injective hle)
  obtain ⟨m, hm⟩ := exists_conj_mem_sylow (T.subtype hTM) hp
  exact ⟨m, m.property, hm⟩

public theorem p_element_fusion [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    {z : G} (hzT : z ∈ (T : Subgroup G))
    (hzcentral : ∀ t ∈ (T : Subgroup G), Commute z t)
    (hunique : ∃! q : G ⧸ M, z • q = q)
    {x y : G} (hxM : x ∈ M) (hyM : y ∈ M)
    (hx : IsPGroup p (zpowers x)) (hxy : IsConj x y) :
    ∃ m ∈ M, m * x * m⁻¹ = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have hy : IsPGroup p (zpowers y) := by
    have hle : zpowers y ≤ (zpowers x).map (MulAut.conj g).toMonoidHom :=
      zpowers_le.mpr ⟨x, mem_zpowers x, hg⟩
    exact (hx.map _).of_injective (inclusion hle) (inclusion_injective hle)
  obtain ⟨a, haM, ha⟩ := p_element_conjugate_into_sylow T hTM hxM hx
  obtain ⟨b, hbM, hb⟩ := p_element_conjugate_into_sylow T hTM hyM hy
  have hab : IsConj (a * x * a⁻¹) (b * y * b⁻¹) := by
    apply isConj_iff.mpr
    refine ⟨b * g * a⁻¹, ?_⟩
    calc
      _ = b * (g * x * g⁻¹) * b⁻¹ := by group
      _ = _ := by rw [hg]
  obtain ⟨m, hmM, hm⟩ := sylow_fusion T hTM hzT hzcentral hunique ha hb hab
  refine ⟨b⁻¹ * m * a, M.mul_mem (M.mul_mem (M.inv_mem hbM) hmM) haM, ?_⟩
  calc
    (b⁻¹ * m * a) * x * (b⁻¹ * m * a)⁻¹ = b⁻¹ * (m * (a * x * a⁻¹) * m⁻¹) * b := by group
    _ = y := by rw [hm]; group
end UniqueFixedCoset
