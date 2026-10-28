module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.FixedLines.FirstPair
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The invariant plane carried by the terminal fixed-line selection

A moved line in the original critical Z-layer has the full critical
commutator as its displacement. These two distinct lines span an invariant
four-group whose fixed subgroup is exactly the critical commutator.
The application keeps the actual conjugator of the first simultaneous
selection, its original fixed line, and its critical image of order two.

This supplies the precise local action left by the terminal selection; the
further same-pair argument excluding that image remains a source obligation.
Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), printed p.892,
the penultimate paragraph.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem eq_of_nontrivial_le_line {G : Type*} [Group G]
    {A C : Subgroup G} (hC : Nat.card C = 2) (hAC : A ≤ C) (hne : A ≠ ⊥) : A = C := by
  let : Finite C := Nat.finite_of_card_ne_zero (by omega)
  let : Finite A := Finite.of_injective (inclusion hAC) (inclusion_injective _)
  exact eq_of_le_of_card_ge hAC (by
    have hpos := (one_lt_card_iff_ne_bot A).mpr hne
    omega)

/-- Movement of a selected line detects the entire original critical commutator. -/
theorem critical_moved_line_commutator (common : CommonFacts R source geometry)
    {c e : Vertex R} (p : CriticalPath R geometry c e)
    {F : Subgroup (FreeAmalgam R)} (hF : F ≤ Z R c)
    (hmove : ¬ Z R e ≤ normalizer F) :
    ⁅F, Z R e⁆ = ⁅Z R c, Z R e⁆ := by
  apply eq_of_nontrivial_le_line (critical_commutator_card common p)
    (commutator_mono hF le_rfl)
  intro hz
  exact hmove (le_normalizer_iff_commutator_le_left.mpr (hz.le.trans bot_le))

/-- The selected line and its displacement span the literal invariant plane;
its fixed subgroup is precisely the original critical commutator. -/
theorem critical_moved_line_plane (common : CommonFacts R source geometry)
    {c e : Vertex R} (p : CriticalPath R geometry c e)
    {F : Subgroup (FreeAmalgam R)} (hF : F ≤ Z R c) (hcard : Nat.card F = 2)
    (hmove : ¬ Z R e ≤ normalizer F) :
    Disjoint F ⁅Z R c, Z R e⁆ ∧
      Nat.card (F ⊔ ⁅Z R c, Z R e⁆ : Subgroup (FreeAmalgam R)) = 4 ∧
      Z R e ≤ normalizer (F ⊔ ⁅Z R c, Z R e⁆ : Subgroup (FreeAmalgam R)) ∧
      (F ⊔ ⁅Z R c, Z R e⁆) ⊓ centralizer (Z R e : Set (FreeAmalgam R)) =
        ⁅Z R c, Z R e⁆ := by
  let E := Z R e
  let C := ⁅Z R c, Z R e⁆
  let P := F ⊔ C
  have hb : 2 < geometry.b R := common.large_distance
  have hCZ : C ≤ Z R c := le_normalizer_iff_commutator_le_left.mp
    ((p.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R c))
  have hCE : C ≤ E := le_normalizer_iff_commutator_le_right.mp
    (((p.reverse common).endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R e))
  have hCcard : Nat.card C = 2 := critical_commutator_card common p
  let : Finite C := Nat.finite_of_card_ne_zero (by omega)
  let := geometry.Z_elementary (by omega) c p.start_color
  let := geometry.Z_elementary (by omega) e p.end_color
  have hcentral : C ≤ centralizer (E : Set (FreeAmalgam R)) :=
    hCE.trans ((le_centralizer_iff_isMulCommutative).mpr inferInstance)
  have hnormC : E ≤ normalizer C :=
    (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hFC : C ≤ normalizer F := by
    apply (show C ≤ centralizer (F : Set (FreeAmalgam R)) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    exact hCZ.trans (((le_centralizer_iff_isMulCommutative).mpr inferInstance).trans
      (centralizer_le hF))
  have hd : Disjoint F C := by
    apply disjoint_iff.mpr
    by_contra hn
    have he : F ⊓ C = F := eq_of_nontrivial_le_line hcard inf_le_left hn
    have hFC' : F ≤ C := he ▸ (show F ⊓ C ≤ C from inf_le_right)
    have heq : F = C := eq_of_le_of_card_ge hFC' (by omega)
    exact hmove (heq ▸ hnormC)
  have hPcard : Nat.card P = 4 := by
    change Nat.card (F ⊔ C : Subgroup (FreeAmalgam R)) = 4
    rw [card_sup_eq_mul_of_normalizes_of_disjoint F C hFC hd, hcard, hCcard]
  have hcomm : ⁅F, E⁆ = C := critical_moved_line_commutator common p hF hmove
  have hnorm : E ≤ normalizer P := by
    apply le_normalizer_iff.mpr
    intro z hz x hx
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left F C hFC] at hx
    obtain ⟨f,hf,y,hy,rfl⟩ := hx
    have hzf : z * f * z⁻¹ ∈ P := by
      have hc : ⁅z,f⁆ ∈ C := by
        rw [← hcomm, commutator_comm]
        exact commutator_mem_commutator hz hf
      have hh := P.mul_mem (mem_sup_right hc) (mem_sup_left hf)
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    have hzy : z * y * z⁻¹ ∈ C := le_normalizer_iff.mp hnormC z hz y hy
    have hh := P.mul_mem hzf (mem_sup_right hzy)
    simpa only [mul_assoc, inv_mul_cancel_left] using hh
  have hfixed : P ⊓ centralizer (E : Set (FreeAmalgam R)) = C := by
    have hlow : C ≤ P ⊓ centralizer (E : Set (FreeAmalgam R)) :=
      le_inf le_sup_right hcentral
    let : Finite P := Nat.finite_of_card_ne_zero (by omega)
    let : Finite ↥(P ⊓ centralizer (E : Set (FreeAmalgam R))) :=
      Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
    have hproper : P ⊓ centralizer (E : Set (FreeAmalgam R)) ≠ P := by
      intro he
      exact hmove (((show F ≤ P from le_sup_left).trans
        (he ▸ (show P ⊓ centralizer (E : Set (FreeAmalgam R)) ≤ centralizer (E : Set (FreeAmalgam R)) from inf_le_right)))
        |> le_centralizer_iff.mp |>.trans (Subgroup.centralizer_le_normalizer _))
    have hlt : Nat.card (P ⊓ centralizer (E : Set (FreeAmalgam R)) : Subgroup (FreeAmalgam R)) < 4 := by
      by_contra! hge
      exact hproper (eq_of_le_of_card_ge inf_le_left (by omega))
    have hdiv := card_dvd_of_le (show P ⊓ centralizer (E : Set (FreeAmalgam R)) ≤ P from inf_le_left)
    rw [hPcard] at hdiv
    have hsmall : Nat.card (P ⊓ centralizer (E : Set (FreeAmalgam R)) : Subgroup (FreeAmalgam R)) ≤ 2 := by
      have h := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 4 ≠ 0)⟩
      rw [show Nat.divisors 4 = {1, 2, 4} by decide] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      omega
    exact (eq_of_le_of_card_ge hlow (by omega)).symm
  exact ⟨hd, hPcard, hnorm, hfixed⟩

/-- The plane has no fixed-core error: its intersection with the source D
at the same vertex is trivial. The full fixed core is not identified with Z. -/
theorem critical_moved_plane_disjoint_fixedCore (common : CommonFacts R source geometry)
    {c e : Vertex R} (p : CriticalPath R geometry c e)
    {F : Subgroup (FreeAmalgam R)} (hF : F ≤ Z R c) (hcard : Nat.card F = 2)
    (hmove : ¬ Z R e ≤ normalizer F) :
    Disjoint (F ⊔ ⁅Z R c, Z R e⁆) (fixedCore R c) := by
  have hb : 2 < geometry.b R := common.large_distance
  have hCZ : ⁅Z R c, Z R e⁆ ≤ Z R c := le_normalizer_iff_commutator_le_left.mp
    ((p.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R c))
  have hCU : ⁅Z R c, Z R e⁆ ≤ U R c := by
    rw [(naturalStructure common).critical_commutator_eq geometry c p.start_color e p.critical]
    exact le_normalizer_iff_commutator_le_left.mp
      (source.critical_U_mutually_normalize geometry c p.start_color e p.critical).2
  have hPZ : F ⊔ ⁅Z R c, Z R e⁆ ≤ Z R c := sup_le hF hCZ
  have hcenter := Escape.Propagation.Rigidity.Z_inf_fixedCore_le_localCenter source c p.start_color
  have hcent : (F ⊔ ⁅Z R c, Z R e⁆) ⊓ fixedCore R c ≤
      Escape.localCenter c := (inf_le_inf_right _ hPZ).trans hcenter
  have hE : Z R e ≤ stabilizer R c := p.endpoint_Z_le_start_stabilizer (by omega)
  have hfixed : (F ⊔ ⁅Z R c, Z R e⁆) ⊓ fixedCore R c ≤
      centralizer (Z R e : Set (FreeAmalgam R)) := by
    rw [Escape.Propagation.Rigidity.localCenter_eq] at hcent
    exact hcent.trans (inf_le_right.trans (centralizer_le hE))
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  rw [← Escape.Propagation.Rigidity.U_inf_localCenter_eq_bot (moduleFacts common) c p.start_color]
  have hbound : (F ⊔ ⁅Z R c, Z R e⁆) ⊓ fixedCore R c ≤ ⁅Z R c, Z R e⁆ := by
    exact (le_inf inf_le_left hfixed).trans
      (critical_moved_line_plane common p hF hcard hmove).2.2.2.le
  exact le_inf (hbound.trans hCU) hcent

/-- The first simultaneous selection carries its exact invariant plane and
the residual index-two pairing, on one and the same conjugator. -/
theorem first_selection_plane (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hnot : ¬ edgeFixedNatural (R := R) w.backward t ≤ fixedCore R c) :
    ∃ g ∈ stabilizer R c,
      let F := edgeFixedNatural (R := R) (act R g w.backward) (act R g t)
      let C := edgeFixedNatural (R := R) c (w.path.walk.getVert 1)
      (¬ Z R n.vertex ≤ normalizer F) ∧
      (¬ Z R n.vertex ≤ normalizer (Z R (act R g w.backward) ⊔ Z R c : Subgroup (FreeAmalgam R))) ∧
      (Q R w.predecessor).relIndex (Z R (act R g w.backward)) = 2 ∧
      ⁅F, Z R n.vertex⁆ = C ∧ Disjoint F C ∧
      Nat.card (F ⊔ C : Subgroup (FreeAmalgam R)) = 4 ∧
      Z R n.vertex ≤ normalizer (F ⊔ C : Subgroup (FreeAmalgam R)) ∧
      (F ⊔ C) ⊓ centralizer (Z R n.vertex : Set (FreeAmalgam R)) = C ∧
      Disjoint (F ⊔ C) (fixedCore R c) := by
  obtain ⟨g,hg,hgF,hgJ,hi⟩ := first_selection_index_two common hb ha hd w n hdt hct hnot
  refine ⟨g,hg,?_⟩
  dsimp only
  have hgc : act R g c = c := hg
  have hgd : color R (act R g w.backward) = false :=
    (action_preserves_color R g w.backward).trans (w.backward_color ha)
  have hgt := (adjacent_act_iff R g w.backward t).mpr hdt
  have hcgt : Adjacent R c (act R g t) := by
    simpa only [hgc] using (adjacent_act_iff R g c t).mpr hct
  have hF := fixed_line_le_common_Z (geometry := geometry) (by omega)
    hgd w.path.start_color hgt hcgt
  have hcard := fixed_line_card common hb ha hd w n hgd hgt
  have heq : ⁅Z R c, Z R n.vertex⁆ = edgeFixedNatural (R := R) c (w.path.walk.getVert 1) := by
    rw [commutator_comm]
    exact (n.pairing common hb ha hd).2.2.2.1
  have hcomm := critical_moved_line_commutator common (n.criticalPath common hb ha hd) hF hgF
  have hplane := critical_moved_line_plane common (n.criticalPath common hb ha hd) hF hcard hgF
  have hdisj := critical_moved_plane_disjoint_fixedCore common
    (n.criticalPath common hb ha hd) hF hcard hgF
  rw [heq] at hcomm hplane hdisj
  exact ⟨hgF,hgJ,hi,hcomm,hplane.1,hplane.2.1,hplane.2.2.1,hplane.2.2.2,hdisj⟩

/-- The reversed selection carries the same critical fixed line and its
natural plane, together with the transported D-containment. A single
transporter is used for both the ordered pair and the source fixed line. -/
theorem second_selection_plane (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hcore : edgeFixedNatural (R := R) w.backward t ≤ fixedCore R c) :
    ∃ g : FreeAmalgam R, act R g w.backward = c ∧
      let F := edgeFixedNatural (R := R) c (act R g t)
      let C := edgeFixedNatural (R := R) c (w.path.walk.getVert 1)
      (¬ Z R n.vertex ≤ normalizer F) ∧
      (¬ Z R n.vertex ≤ normalizer (Z R (act R g c) ⊔ Z R c : Subgroup (FreeAmalgam R))) ∧
      Nonempty (CriticalPath R geometry (act R g c) w.predecessor) ∧
      F ≤ fixedCore R (act R g c) ∧
      ⁅F, Z R n.vertex⁆ = C ∧ Disjoint F C ∧
      Nat.card (F ⊔ C : Subgroup (FreeAmalgam R)) = 4 ∧
      F ⊔ C ≤ U R c ∧
      Z R n.vertex ≤ normalizer (F ⊔ C : Subgroup (FreeAmalgam R)) ∧
      (F ⊔ C) ⊓ centralizer (Z R n.vertex : Set (FreeAmalgam R)) = C ∧
      Disjoint (F ⊔ C) (fixedCore R c) := by
  obtain ⟨g,hg,hgF,hgJ,hp,hD⟩ :=
    second_selection_core_transport common hb ha hd w n hdt hct hcore
  refine ⟨g,hg,?_⟩
  dsimp only
  have hgt : Adjacent R c (act R g t) := by
    simpa only [hg] using (adjacent_act_iff R g w.backward t).mpr hdt
  have hF : edgeFixedNatural (R := R) c (act R g t) ≤ Z R c :=
    inf_le_left.trans (U_le_Z R c)
  have hcard := fixed_line_card common hb ha hd w n w.path.start_color hgt
  have heq : ⁅Z R c, Z R n.vertex⁆ = edgeFixedNatural (R := R) c (w.path.walk.getVert 1) := by
    rw [commutator_comm]
    exact (n.pairing common hb ha hd).2.2.2.1
  have hcomm := critical_moved_line_commutator common (n.criticalPath common hb ha hd) hF hgF
  have hplane := critical_moved_line_plane common (n.criticalPath common hb ha hd) hF hcard hgF
  have hdisj := critical_moved_plane_disjoint_fixedCore common
    (n.criticalPath common hb ha hd) hF hcard hgF
  rw [heq] at hcomm hplane hdisj
  exact ⟨hgF,hgJ,hp,hD,hcomm,hplane.1,hplane.2.1,
    sup_le inf_le_left inf_le_left,hplane.2.2.1,hplane.2.2.2,hdisj⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
