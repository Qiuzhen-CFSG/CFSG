module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.Displacement
public import CFSG.Quasithin.Chapter10.SourceA5OriginalFixedPair
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterAction
public import Theory.GroupTheory.SylowNormalJoinIntersection

/-!
# Original fixed vectors in the actual fixed-center moved module

The Sylow intersections of the two commuting original blocks generate the
residual Sylow intersection. Conjugation symmetry forces both blocks to move
the actual Sylow-center orbit. Their realized displacement lines are fixed by
the corresponding Sylow intersections, so uniqueness identifies them with the
prescribed original fixed vectors. Their commutator witnesses place both
vectors in the original moved module.

Source: Aschbacher–Smith 10.2.1, printed p.743, using E.2.3(3).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem original_pair_sylow_join
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {t : G}
    (p : SourceA5OriginalFixedPair D t)
    (hgen : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom) :
    (T : Subgroup G) ⊓ localOrbit T L =
      ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ L.map (MulAut.conj t).toMonoidHom) := by
  let N := localOrbit T L
  let B := L.map (MulAut.conj t).toMonoidHom
  have hgen' : N = L ⊔ B := hgen
  have hLN : L ≤ N := by rw [hgen']; exact le_sup_left
  have hBN : B ≤ N := by rw [hgen']; exact le_sup_right
  have hnormal : (N.subgroupOf (localJoin T L)).Normal :=
    normal_subgroupOf_of_le_normalizer
      (sup_le N.le_normalizer (le_normalizer_componentOrbit L T))
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (show Chapter1.IsSylowIn 2 (T : Subgroup G) (localJoin T L) from
      ⟨T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right),
       map_subgroupOf_eq_of_le le_sup_right⟩)
    (show N ≤ localJoin T L from le_sup_left) hnormal.isSubnormal
  have hLB : L ≤ centralizer (B : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp p.blocks_commute
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (by
      rw [hgen']
      exact sup_le L.le_normalizer
        ((le_centralizer_iff.mp hLB).trans (centralizer_le_normalizer L)))
  let : (B.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (by rw [hgen']; exact sup_le (hLB.trans (centralizer_le_normalizer B)) B.le_normalizer)
  have hh := P.inf_sup_eq_sup_inf_normal (L.subgroupOf N) (B.subgroupOf N)
  have htop : L.subgroupOf N ⊔ B.subgroupOf N = ⊤ := by
    rw [←subgroupOf_sup hLN hBN,←hgen,subgroupOf_self]
  rw [htop,inf_top_eq] at hh
  have hm := congrArg (map N.subtype) hh
  rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ N.subtype_injective,
    Subgroup.map_inf _ _ _ N.subtype_injective,hP,
    map_subgroupOf_eq_of_le hLN,map_subgroupOf_eq_of_le hBN] at hm
  simpa only [inf_assoc,inf_eq_right.mpr hLN,inf_eq_right.mpr hBN] using hm

omit [Finite G] in
private theorem displacement_line_fixed
    (P W : Subgroup G) (hn : P ≤ normalizer (W : Set G)) {v : G}
    (hline : ∀ g∈P, ∀ x∈W, ⁅g,x⁆=1 ∨ ⁅g,x⁆=v)
    (hvn : v ≠ 1) (hwitness : ∃ g∈P, ∃ x∈W, ⁅g,x⁆=v) :
    v ∈ centralizer (P : Set G) := by
  obtain ⟨g,hg,x,hx,he⟩ := hwitness
  intro r hr
  let a := MulAut.conj r
  have hg' : a g ∈ P := (mem_normalizer_iff.mp (P.le_normalizer hr) g).mp hg
  have hx' : a x ∈ W := (mem_normalizer_iff.mp (hn hr) x).mp hx
  have hav : a v = v := by
    have he' : ⁅a g,a x⁆ = a v := by rw [←map_commutatorElement,he]
    have hh := hline (a g) hg' (a x) hx'
    rw [he'] at hh
    exact hh.resolve_left (fun hh => hvn (a.injective (hh.trans (a.map_one).symm)))
  exact mul_inv_eq_iff_eq_mul.mp hav

private theorem original_first_moves
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {t : G}
    (ht : t∈(T : Subgroup G)) (p : SourceA5OriginalFixedPair D t)
    (hgen : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom)
    (W : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hm : ¬ (T : Subgroup G) ⊓ localOrbit T L ≤ centralizer (W : Set G)) :
    ¬ (T : Subgroup G) ⊓ L ≤ centralizer (W : Set G) := by
  intro hfix
  have hT : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
  have hW : W.map (MulAut.conj t).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (hn ht)
  have hfixB := map_mono (f := (MulAut.conj t).toMonoidHom) hfix
  rw [map_inf _ _ _ (MulAut.conj t).injective,hT,
    Theory.GroupTheory.map_centralizer_equiv] at hfixB
  change (T : Subgroup G) ⊓ L.map (MulAut.conj t).toMonoidHom ≤
    centralizer (W.map (MulAut.conj t).toMonoidHom : Set G) at hfixB
  rw [hW] at hfixB
  exact hm ((original_pair_sylow_join D p hgen).symm ▸ sup_le hfix hfixB)

/-- The unique original fixed vector is a realized displacement on the actual
Sylow-center orbit. This retains the prescribed original conjugate pair. -/
theorem source_a5_original_first_displacement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t∈(T : Subgroup G)) (p : SourceA5OriginalFixedPair D t)
    (hgen : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom)
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hWE : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H ≤
      omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G))) :
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
    p.first ∈ W ∧ p.first ∈ ⁅W,H⁆ ∧
      (∀ g∈(T : Subgroup G) ⊓ L, ∀ x∈W, ⁅g,x⁆=1 ∨ ⁅g,x⁆=p.first) ∧
      ∃ g∈(T : Subgroup G) ⊓ L, ∃ x∈W, ⁅g,x⁆=p.first := by
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    hH.1.1.2.trans (le_normalizer_conjugateSpanBy _ _)
  have hmove := original_first_moves D ht p hgen W hTW
    (source_a5_fixed_center_orbit_action D e hn hne H hH)
  obtain ⟨g,hg,hgc⟩ := SetLike.not_le_iff_exists.mp hmove
  obtain ⟨x,hx,hgx⟩ : ∃ x∈W, ⁅g,x⁆≠1 := by
    by_contra! hh
    exact hgc (fun x hx => (commutatorElement_eq_one_iff_mul_comm.mp (hh x hx)).symm)
  obtain ⟨v,hv,hvn,hline⟩ := source_a5_original_baumann_displacement D e hn hout
  have hlineW : ∀ g∈(T : Subgroup G) ⊓ L, ∀ x∈W, ⁅g,x⁆=1 ∨ ⁅g,x⁆=v :=
    fun g hg x hx => hline g hg x (hWE hx)
  have he : ⁅g,x⁆=v := (hlineW g hg x hx).resolve_left hgx
  have hf := displacement_line_fixed _ W (inf_le_left.trans hTW) hlineW hvn
    ⟨g,hg,x,hx,he⟩
  have hvp : v = p.first := p.first_unique v hv hf hvn
  rw [hvp] at hlineW he
  refine ⟨?_,?_,hlineW,g,hg,x,hx,he⟩
  · rw [←he]
    exact W.mul_mem ((mem_normalizer_iff.mp (hTW hg.1) x).mp hx) (W.inv_mem hx)
  · rw [←he,commutator_comm]
    exact commutator_mem_commutator (hH.1.1.2 hg.1) hx

/-- Both prescribed vectors lie in the actual moved module, and commuting
original block actors realize their two displacement lines. -/
theorem source_a5_original_pair_displacements
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t∈(T : Subgroup G)) (htn : t∉normalizer (L : Set G))
    (p : SourceA5OriginalFixedPair D t)
    (hgen : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom)
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hWE : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H ≤
      omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G))) :
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
    p.first ∈ W ∧ p.second ∈ W ∧ p.first ∈ ⁅W,H⁆ ∧ p.second ∈ ⁅W,H⁆ ∧
      p.first ≠ p.second ∧
      ∃ g₁ g₂ : G, g₁∈(T : Subgroup G) ⊓ L ∧
        g₂∈(T : Subgroup G) ⊓ L.map (MulAut.conj t).toMonoidHom ∧
        Commute g₁ g₂ ∧
        (∀ x∈W, ⁅g₁,x⁆=1 ∨ ⁅g₁,x⁆=p.first) ∧
        (∀ x∈W, ⁅g₂,x⁆=1 ∨ ⁅g₂,x⁆=p.second) ∧
        (∃ x∈W, ⁅g₁,x⁆=p.first) ∧ (∃ x∈W, ⁅g₂,x⁆=p.second) := by
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  obtain ⟨hvW,hvM,hline,g,hg,x,hx,he⟩ :=
    source_a5_original_first_displacement D e hn hne hout ht p hgen H hH hWE
  let a := MulAut.conj t
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
    hH.1.1.2.trans (le_normalizer_conjugateSpanBy _ _)
  have haW : ∀ y∈W, a y∈W := fun y hy => (mem_normalizer_iff.mp (hTW ht) y).mp hy
  have haT : ∀ y∈(T : Subgroup G), a y∈(T : Subgroup G) :=
    fun y hy => (mem_normalizer_iff.mp ((T : Subgroup G).le_normalizer ht) y).mp hy
  have hp2W : p.second∈W := by
    rw [p.conjugate]
    exact haW p.first hvW
  have hp2M : p.second∈⁅W,H⁆ := by
    rw [p.conjugate]
    exact (mem_normalizer_iff.mp (normalizer_commutator_ge_right W H (hH.1.1.2 ht)) _).mp hvM
  have hne12 : p.first ≠ p.second := by
    intro heq
    apply htn
    have hf : t∈centralizer ({p.first} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      exact mul_inv_eq_iff_eq_mul.mp (p.conjugate.symm.trans heq.symm)
    exact (p.first_centralizer ▸ (show t∈(T : Subgroup G)⊓centralizer ({p.first} : Set G) from ⟨ht,hf⟩)).2
  have hg₂ : a g∈(T : Subgroup G)⊓L.map a.toMonoidHom :=
    ⟨haT g hg.1,mem_map_of_mem a.toMonoidHom hg.2⟩
  have hline₂ : ∀ y∈W, ⁅a g,y⁆=1 ∨ ⁅a g,y⁆=p.second := by
    intro y hy
    have hy' : a.symm y∈W := by
      simpa only [a,MulAut.conj_symm_apply,inv_inv] using
        (mem_normalizer_iff.mp (hTW ((T : Subgroup G).inv_mem ht)) y).mp hy
    have hh := (hline g hg (a.symm y) hy').imp
      (congrArg a) (congrArg a)
    simpa only [map_commutatorElement,a.apply_symm_apply,map_one,
      show a p.first = p.second from p.conjugate.symm] using hh
  refine ⟨hvW,hp2W,hvM,hp2M,hne12,g,a g,hg,hg₂,?_,hline g hg,hline₂,
    ⟨x,hx,he⟩,a x,haW x hx,?_⟩
  · exact (commutator_eq_bot_iff_le_centralizer.mp p.blocks_commute hg.2) (a g) hg₂.2 |>.symm
  · rw [←map_commutatorElement,he]
    exact p.conjugate.symm

end CFSG.Quasithin.Chapter10
