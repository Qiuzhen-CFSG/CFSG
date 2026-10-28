module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.DistanceGap
public import Theory.Representation.BinaryConjugationSection.SupportImages

/-!
# The two-part of the terminal section action kernel

An element fixing V_t/Z_t normalizes every neighboring center, because
Z_t lies in each of them. Distinct neighbors have distinct centers, so this
element fixes the full neighbor set and belongs to U_t. The normal Sylow
two-subgroup Q_t of U_t then shows that every Sylow two-subgroup acts
faithfully after passage to L_t/Q_t.

The final theorem transports the epsilon-two seed along the actual graph
and applies this argument to the literal terminal section. It does not
identify U_t with Q_t or discard a possible odd action kernel.
Source: DGS, *Groups and Graphs* (1985), (6.2)(d), (7.4)--(7.5),
printed pp.119,128--131.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The literal radius-section kernel fixes the entire closed neighborhood. -/
theorem graph_radius_section_kernel_le_U (h : LocallyRankOneTriple P B)
    {t y : Vertex (family P)} (hty : (graph (family P)).Adj t y)
    (hZZ : Z (family P) t ≤ Z (family P) y)
    {H : Subgroup G} (hH : H ≤ stabilizer (family P) t)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W}
    (s : BinaryConjugationSection H (V (family P) t 1) (Z (family P) t) ρ) :
    ρ.ker.map H.subtype ≤ U (family P) t := by
  let := finite_endpoints h
  have hseed (x : Vertex (family P)) (htx : (graph (family P)).Adj t x) :
      Z (family P) t ≤ Z (family P) x := by
    obtain ⟨g,hg,hgx⟩ := locally_transitive (family P) hty htx
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hZZ
    rwa [←Z_translate,←Z_translate,show g • t = t from hg,hgx] at hm
  rintro _ ⟨k,hk,rfl⟩ x hx
  rcases (mem_ball_one _ _ _).mp hx with htx | rfl
  · have hZX : Z (family P) x ≤ V (family P) t 1 :=
      le_iSup_of_le x (le_iSup_of_le hx le_rfl)
    have hkn : (k : G) ∈ normalizer (Z (family P) x : Set G) := by
      have hm : k ∈ subspaceStabilizer ρ (s.imageSpace (Z (family P) x)) := by
        intro w
        rw [show ρ k = 1 from hk]
        rfl
      rwa [s.subspaceStabilizer_imageSpace _ hZX (hseed x htx)] at hm
    have he : Z (family P) ((k : G) • x) = Z (family P) x := by
      rw [Z_translate]
      exact mem_normalizer_iff_map_conj_eq.mp hkn
    by_contra hne
    have hadj : (graph (family P)).Adj t ((k : G) • x) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) (k : G)).map_adj_iff.mpr htx
      change (graph (family P)).Adj ((k : G) • t) ((k : G) • x) at hh
      rwa [show (k : G) • t = t from hH k.property] at hh
    exact graph_neighbor_centers_ne h hadj htx hne he
  · exact hH k.property

/-- The same quotient action has trivial kernel on each actual Sylow two-subgroup. -/
theorem graph_radius_section_sylow_kernel (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    {t y : Vertex (family P)} (hty : (graph (family P)).Adj t y)
    (hZZ : Z (family P) t ≤ Z (family P) y)
    {H : Subgroup G} (hH : H ≤ stabilizer (family P) t)
    [((Q (family P) t).subgroupOf H).Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ (Q (family P) t).subgroupOf H) W)
    (s : BinaryConjugationSection H (V (family P) t 1) (Z (family P) t)
      (σ.comp (QuotientGroup.mk' ((Q (family P) t).subgroupOf H))))
    (S : Sylow 2 H) :
    Disjoint σ.ker
      ((S : Subgroup H).map (QuotientGroup.mk' ((Q (family P) t).subgroupOf H))) := by
  let π := QuotientGroup.mk' ((Q (family P) t).subgroupOf H)
  let R := (S : Subgroup H).map H.subtype
  have hnorm : U (family P) t ≤ normalizer (Q (family P) t : Set G) := by
    apply (U_le_stabilizer _ _).trans
    exact (stabilizer (family P) t).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hi := inf_eq_inf_of_normal_sylow R (U (family P) t) (Q (family P) t)
    (S.isPGroup'.map _) (source_Z_Q_U h t).2 hnorm (hS t)
  have hk := graph_radius_section_kernel_le_U h hty hZZ hH s
  apply disjoint_iff.mpr
  apply bot_unique
  rintro x ⟨hxk,l,hl,rfl⟩
  have hlu : (l : G) ∈ U (family P) t := hk ⟨l,hxk,rfl⟩
  have hlq : (l : G) ∈ Q (family P) t :=
    (hi.le ⟨mem_map_of_mem H.subtype hl,hlu⟩).2
  exact (QuotientGroup.eq_one_iff l).mpr hlq

private theorem center_inclusion_of_type (h : LocallyRankOneTriple P B)
    {u v t y : Vertex (family P)} (huv : (graph (family P)).Adj u v)
    (hty : (graph (family P)).Adj t y) (htype : u.type = t.type)
    (hZZ : Z (family P) u ≤ Z (family P) v) :
    Z (family P) t ≤ Z (family P) y := by
  let := finite_endpoints h
  obtain ⟨g,hgu⟩ := (same_orbit_iff (family P) u t).mpr htype
  have htg : (graph (family P)).Adj t (g • v) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr huv
    change (graph (family P)).Adj (g • u) (g • v) at hh
    rwa [hgu] at hh
  obtain ⟨r,hr,hry⟩ := locally_transitive (family P) htg hty
  have hm := map_mono (f := (MulAut.conj (r*g)).toMonoidHom) hZZ
  rwa [←Z_translate,←Z_translate,mul_smul,mul_smul,hgu,
    show r • t = t from hr,hry] at hm

/-- The epsilon-two source seed gives faithful Sylow action on the terminal
section, with no faithful-action or local-model premise. -/
theorem graph_epsilonTwo_terminal_sylow_kernel
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    {v u t y : Vertex (family P)} (hvu : (graph (family P)).Adj v u)
    (hty : (graph (family P)).Adj t y) (htype : v.type = y.type)
    (c₀ : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) u))
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer (family P) v))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    {H : Subgroup G} (hH : H ≤ stabilizer (family P) t)
    [((Q (family P) t).subgroupOf H).Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ (Q (family P) t).subgroupOf H) W)
    (s : BinaryConjugationSection H (V (family P) t 1) (Z (family P) t)
      (σ.comp (QuotientGroup.mk' ((Q (family P) t).subgroupOf H))))
    (S : Sylow 2 H) :
    Disjoint σ.ker
      ((S : Subgroup H).map (QuotientGroup.mk' ((Q (family P) t).subgroupOf H))) := by
  have hut : u.type = t.type := by
    have hu := hvu.1
    have ht := hty.1
    cases hv : v.type <;> cases hu' : u.type <;>
      cases ht' : t.type <;> cases hy : y.type <;> simp_all
  have hZZ : Z (family P) u ≤ Z (family P) v :=
    hepsilon.le.trans (graph_edgeSeed_le_Z h hB hvu c₀ ho₀)
  exact graph_radius_section_sylow_kernel h hS hty
    (center_inclusion_of_type h hvu.symm hty hut hZZ) hH σ s S

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
