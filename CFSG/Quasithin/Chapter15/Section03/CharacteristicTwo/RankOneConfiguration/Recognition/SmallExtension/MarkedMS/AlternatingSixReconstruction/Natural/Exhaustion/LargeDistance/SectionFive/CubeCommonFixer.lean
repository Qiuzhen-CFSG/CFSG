module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelOrbit
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePlane
public import Theory.GroupAction.SymmetricSixSmallSection

/-!
# Simultaneous parabolic kernels and the strict small-image shift

In the three-pair branch, the small critical image is a transposition. Choose
simultaneously a conjugate three-pair group and a cubic so that the group
and its cubic conjugate generate S₆, and the group together with the two
critical transpositions also generates S₆. In canonical coordinates these
are the matching (02)(14)(35), the rotation (024)(135), and (01). Each
asserted generation follows from a chain of adjacent transpositions.

Lift this one choice through the actual symmetric quotient and its entire
two-core kernel. The selected graph neighborhood kernel is identified with
the embedded two-core of the inverse image of the same plane parabolic.
Thus the entire selected radical, including every local Thompson subgroup
inside it, lies in that parabolic kernel. No identification with a kernel
at a different graph vertex or with the exceptional graph is used.

The selected kernel and its conjugate generate the whole starting
stabilizer. This supplies the common-fixer bound of MS93 (5.6)(b) directly,
on both full central covers and with every central attachment retained.
For two trapped paths, both obstruction lines centralize the selected
kernel. The existing conjugate-line equality puts the first line in the
conjugate kernel's fixer as well. It is therefore centralized by the whole
starting stabilizer, contradicting the retained nonnormalization witness.
The strict slice index greater than two is used to obtain that witness.

The original nonsylow consumer constructs the action and full three-pair
image internally. It retains the same selected neighbor transporter, cubic,
generating pair, and overlapping walks, and eliminates both orientations
of the trapped alternative. The revised simultaneous choice has two
generating kernels; the earlier selector that normalizes its selected
kernel remains available at its original, weaker conclusion. This proves
the strict small-image backward-shift application, not the unconditional
distance bound or all clauses of the general source selection theorem.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6)(b) and (5.7), printed pp.917--919; (3.3)(ii), pp.866--867;
characteristic reduction, pp.932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace CubeCommonFixer
local notation "S" => Equiv.Perm (Fin 6)
private abbrev t : S := Equiv.swap 0 1
private abbrev r : S := BinaryFlags.pairRotation
private abbrev k : S := Equiv.swap 1 2 * Equiv.swap 3 4
private abbrev D' : Subgroup S := (D 6).map (MulAut.conj k).toMonoidHom

private theorem chain_generates (v : S) (N : Subgroup S)
    (hv : ∀ i : Fin 5, (MulAut.conj v) (Equiv.swap i.castSucc i.succ) ∈ N) : N = ⊤ := by
  apply top_unique
  have hh := congrArg (Subgroup.map (MulAut.conj v).toMonoidHom)
    (Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5))
  rw [map_top_of_surjective (MulAut.conj v).toMonoidHom (MulAut.conj v).surjective] at hh
  rw [←hh,Subgroup.map_le_iff_le_comap,closure_le]
  rintro _ ⟨i,rfl⟩
  exact hv i

private theorem pair_generates :
    D' ⊔ zpowers t ⊔ zpowers ((MulAut.conj r) t) = ⊤ := by
  let v : S := Equiv.swap 0 4 * Equiv.swap 2 4 * Equiv.swap 3 4
  apply chain_generates v
  intro i
  have cert : ∀ i : Fin 5,
      (∃ j : Fin 3, (MulAut.conj v) (Equiv.swap i.castSucc i.succ) =
        (MulAut.conj k) (pairSwap 6 j)) ∨
      (MulAut.conj v) (Equiv.swap i.castSucc i.succ) = t ∨
      (MulAut.conj v) (Equiv.swap i.castSucc i.succ) = (MulAut.conj r) t := by
    decide +kernel
  rcases cert i with ⟨j,hj⟩ | hj | hj
  · rw [hj]
    exact mem_sup_left (mem_sup_left (mem_map_of_mem _ (pairSwap_mem (n := 6) (m := 3) j (by omega))))
  · rw [hj]; exact mem_sup_left (mem_sup_right (mem_zpowers _))
  · rw [hj]; exact mem_sup_right (mem_zpowers _)

private theorem kernels_generate : D' ⊔ D'.map (MulAut.conj r).toMonoidHom = ⊤ := by
  let v : S := Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 5 * Equiv.swap 5 3
  apply chain_generates v
  intro i
  have cert : ∀ i : Fin 5, ∃ j : Fin 3,
      (MulAut.conj v) (Equiv.swap i.castSucc i.succ) = (MulAut.conj k) (pairSwap 6 j) ∨
      (MulAut.conj v) (Equiv.swap i.castSucc i.succ) =
        (MulAut.conj r) ((MulAut.conj k) (pairSwap 6 j)) := by
    decide +kernel
  obtain ⟨j,hj | hj⟩ := cert i
  · rw [hj]; exact mem_sup_left (mem_map_of_mem _ (pairSwap_mem (n := 6) (m := 3) j (by omega)))
  · rw [hj]; exact mem_sup_right (mem_map_of_mem _
      (mem_map_of_mem _ (pairSwap_mem (n := 6) (m := 3) j (by omega))))

private theorem swap_conjugator (a : S) (ha : a.IsSwap) :
    ∃ g : alternatingGroup (Fin 6), g.val * t * g.val⁻¹ = a := by
  have hc : IsConj t a := Equiv.Perm.isConj_of_cycleType_eq
    ((by decide +kernel : t.cycleType = {2}).trans
      (Equiv.Perm.isSwap_iff_cycleType.mp ha).symm)
  obtain ⟨c,hc⟩ := isConj_iff.mp hc
  rcases Int.units_eq_one_or (Equiv.Perm.sign c) with he | he
  · exact ⟨⟨c,he⟩,hc⟩
  · have hk : c*t ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup,map_mul,he]
      decide +kernel
    refine ⟨⟨c*t,hk⟩,?_⟩
    change (c*t)*t*(c*t)⁻¹=a
    rw [←hc]
    group


private theorem conjugate_twice (A : Subgroup S) (u v : S) :
    (A.map (MulAut.conj u).toMonoidHom).map (MulAut.conj v).toMonoidHom =
      A.map (MulAut.conj (v*u)).toMonoidHom := by
  rw [map_map]
  congr 1

private theorem inverse_pair (A : Subgroup S) (x : S)
    (hh : A ⊔ A.map (MulAut.conj x).toMonoidHom = ⊤) :
    A ⊔ A.map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
  have he := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hh
  rw [Subgroup.map_sup,conjugate_twice,inv_mul_cancel,
    show (MulAut.conj (1:S)).toMonoidHom = MonoidHom.id S from rfl,
    map_id,map_top_of_surjective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).surjective] at he
  rwa [sup_comm] at he

/-- The same conjugator supplies the two-seed generator and two kernels
with trivial common fixed quotient. -/
private theorem marked_pair (a : S) (ha : a.IsSwap) :
    ∃ v x : S, x ∈ alternatingGroup (Fin 6) ∧ orderOf x=3 ∧
      ((D 6).map (MulAut.conj v).toMonoidHom) ⊔ zpowers a ⊔
        zpowers ((MulAut.conj x) a) = ⊤ ∧
      ((D 6).map (MulAut.conj v).toMonoidHom) ⊔
        ((D 6).map (MulAut.conj v).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
  obtain ⟨c,hc⟩ := swap_conjugator a ha
  let x := (MulAut.conj c.val) r
  have hx : x ∈ alternatingGroup (Fin 6) := by
    have hr : r ∈ alternatingGroup (Fin 6) := by decide +kernel
    exact (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem r hr c.val
  have hro : orderOf r = 3 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have ht : (MulAut.conj c.val).toMonoidHom t = a := hc
  have hrt : (MulAut.conj c.val).toMonoidHom ((MulAut.conj r) t) = (MulAut.conj x) a := by
    rw [←ht]
    change c.val*(r*t*r⁻¹)*c.val⁻¹=
      (c.val*r*c.val⁻¹)*(c.val*t*c.val⁻¹)*(c.val*r*c.val⁻¹)⁻¹
    group
  have hD : D'.map (MulAut.conj c.val).toMonoidHom = (D 6).map (MulAut.conj (c.val*k)).toMonoidHom :=
    conjugate_twice _ _ _
  have hDx : (D'.map (MulAut.conj r).toMonoidHom).map (MulAut.conj c.val).toMonoidHom =
      (D'.map (MulAut.conj c.val).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    rw [conjugate_twice D' r c.val,conjugate_twice D' c.val x]
    have he : c.val*r=x*c.val := by
      change c.val*r=(c.val*r*c.val⁻¹)*c.val
      group
    rw [he]
  refine ⟨c.val*k,x,hx,((MulAut.conj c.val).orderOf_eq r).trans hro,?_,?_⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj c.val).toMonoidHom) pair_generates
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,ht,hrt,hD,
      map_top_of_surjective (MulAut.conj c.val).toMonoidHom (MulAut.conj c.val).surjective] using hh
  · apply inverse_pair
    have hh := congrArg (Subgroup.map (MulAut.conj c.val).toMonoidHom) kernels_generate
    simpa only [Subgroup.map_sup,hDx,hD,
      map_top_of_surjective (MulAut.conj c.val).toMonoidHom (MulAut.conj c.val).surjective] using hh

/-- The full inverse image of the three-pair group is the actual two-core
of the inverse image of its plane parabolic. -/
private theorem full_cube_parabolic_core {F : Type*} [Group F] [Finite F]
    (π : F →* S) (hs : Function.Surjective π) (hp : IsPGroup 2 π.ker)
    (A : Subgroup F) (hk : π.ker ≤ A) (u : S)
    (hA : A.map π = (D 6).map (MulAut.conj u).toMonoidHom) :
    A = ((BinaryFlags.H2.map (MulAut.conj u).toMonoidHom).comap π).pCoreIn 2 := by
  let P := (BinaryFlags.H2.map (MulAut.conj u).toMonoidHom).comap π
  have hkP : π.ker ≤ P := by
    intro z hz
    change π z ∈ BinaryFlags.H2.map (MulAut.conj u).toMonoidHom
    rw [MonoidHom.mem_ker.mp hz]
    exact one_mem _
  have hkcore : π.ker ≤ P.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp hkP le_normalizer_of_normal
  apply map_injective_of_ker_le π hk hkcore
  rw [map_pCoreIn_of_ker_isPGroup π hp,
    map_comap_eq_self_of_surjective hs,
    ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj u).injective,
    BinaryFlags.H2_core_eq_D,SixCorePlane.cube_eq]
  exact hA

end CubeCommonFixer

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

include s in
/-- Simultaneous selection of the literal lifted parabolic two-core, the
cubic, and both generating pairs at the original base vertex. -/
theorem small_cube_common_fixer_neighbor
    (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ v : S, Q d.radical t =
        (((BinaryFlags.H2.map (MulAut.conj v).toMonoidHom).comap s.projection).pCoreIn 2).map
          (embedM d.radical) ∧
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        Q d.radical t ⊔ (Q d.radical t).map (MulAut.conj x).toMonoidHom =
          stabilizer d.radical (alpha d.radical) ∧
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
          stabilizer d.radical (alpha d.radical) := by
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  obtain ⟨k,b,hbeven,hbo,hgen,hpair⟩ := CubeCommonFixer.marked_pair a hswap
  obtain ⟨g,hg⟩ := s.surjective (k*u⁻¹)
  have hbL : b ∈ (replacementComponent d).map s.projection := by
    rw [s.component_image]
    exact hbeven
  obtain ⟨y,hy,hyb⟩ := hbL
  let R₁ := d.radical.map (MulAut.conj g).toMonoidHom
  let A := (Z d.radical a').comap (embedM d.radical)
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hR : R₁.map s.projection = (D 6).map (MulAut.conj k).toMonoidHom := by
    have he : s.projection.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (k*u⁻¹)).toMonoidHom.comp s.projection := by
      apply MonoidHom.ext
      intro v
      change s.projection (g*v*g⁻¹)=(k*u⁻¹)*s.projection v*(k*u⁻¹)⁻¹
      rw [map_mul,map_mul,map_inv,hg]
    change (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection = _
    rw [map_map,he,←map_map,hfull,map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change (k*u⁻¹)*(u*v*u⁻¹)*(k*u⁻¹)⁻¹=k*v*k⁻¹
    group
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hker : s.projection.ker ≤ R₁ := by
    rw [s.projection_kernel,←hQ]
    exact map_mono (replacement_core_le_radical h d)
  have hA₁ : A₁.map s.projection =
      (A.map s.projection).map (MulAut.conj b).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change s.projection (y*v*y⁻¹)=b*s.projection v*b⁻¹
    rw [map_mul,map_mul,map_inv,hyb]
  have htop : R₁ ⊔ A ⊔ A₁ = ⊤ := by
    apply map_injective_of_ker_le s.projection
      (hker.trans (le_sup_left.trans le_sup_left)) le_top
    rw [Subgroup.map_sup,Subgroup.map_sup,hR,hA₁,
      map_top_of_surjective s.projection s.surjective]
    apply top_unique
    rw [←hgen]
    exact sup_le_sup (sup_le_sup_left (zpowers_le.mpr ha) _)
      (zpowers_le.mpr (mem_map_of_mem _ ha))
  have hRpair : R₁ ⊔ R₁.map (MulAut.conj y⁻¹).toMonoidHom = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,map_top_of_surjective s.projection s.surjective]
    have he : (R₁.map (MulAut.conj y⁻¹).toMonoidHom).map s.projection =
        (R₁.map s.projection).map (MulAut.conj b⁻¹).toMonoidHom := by
      rw [map_map (K := R₁) s.projection (MulAut.conj y⁻¹).toMonoidHom,
        map_map (K := R₁) (MulAut.conj b⁻¹).toMonoidHom s.projection]
      apply congrArg (fun f => R₁.map f)
      apply MonoidHom.ext
      intro v
      change s.projection (y⁻¹*v*(y⁻¹)⁻¹)=b⁻¹*s.projection v*(b⁻¹)⁻¹
      simp only [map_mul,map_inv,hyb]
    rw [he,hR]
    exact hpair
  let f := (embedM d.radical g)⁻¹
  let x := (embedM d.radical y)⁻¹
  let t := act d.radical f (beta d.radical)
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have ht : Q d.radical t = R₁.map (embedM d.radical) := by
    rw [Q_act,Q_beta,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change f⁻¹*embedM d.radical v*(f⁻¹)⁻¹=embedM d.radical (g*v*g⁻¹)
    simp only [f,inv_inv,map_mul,map_inv]
  have hxL : x ∈ Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
    exact mem_map_of_mem _ ((replacementComponent d).inv_mem hy)
  have hAm : A.map (embedM d.radical) = Z d.radical a' :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  have hparabolic := CubeCommonFixer.full_cube_parabolic_core s.projection s.surjective
    (s.projection_kernel.symm ▸ pCore_isPGroup) R₁ hker k hR
  refine ⟨t,?_,k,ht.trans (congrArg (Subgroup.map (embedM d.radical)) hparabolic),x,hxL,?_,?_,?_⟩
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hRpair
    rw [Subgroup.map_sup,←ht,←MonoidHom.range_eq_map] at hh
    have he : (R₁.map (MulAut.conj y⁻¹).toMonoidHom).map (embedM d.radical) =
        (Q d.radical t).map (MulAut.conj x).toMonoidHom := by
      rw [ht,map_map (K := R₁) (embedM d.radical) (MulAut.conj y⁻¹).toMonoidHom,
        map_map (K := R₁) (MulAut.conj x).toMonoidHom (embedM d.radical)]
      apply congrArg (fun f => R₁.map f)
      apply MonoidHom.ext
      intro v
      change embedM d.radical (y⁻¹*v*(y⁻¹)⁻¹)=x*embedM d.radical v*x⁻¹
      simp only [x,map_mul,map_inv]
    rw [he] at hh
    exact hh.trans (stabilizer_m_base d.radical).symm
  · have hy3 : y^3 ∈ pCore 2 d.overgroup := by
      rw [←s.projection_kernel,MonoidHom.mem_ker,map_pow,hyb]
      simpa only [hbo] using pow_orderOf_eq_one b
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    have hx3 : x^3=embedM d.radical ((y^3)⁻¹) := by simp only [x,inv_pow,map_inv,map_pow]
    rw [hx3]
    exact mem_map_of_mem _ ((pCore 2 d.overgroup).inv_mem hy3)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop
    rw [Subgroup.map_sup,Subgroup.map_sup,hAm,←ht,←MonoidHom.range_eq_map] at hh
    have hA₁m : A₁.map (embedM d.radical) = Z d.radical (act d.radical x a') := by
      rw [Z_act,←hAm,map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro v
      change embedM d.radical (y*v*y⁻¹)=x⁻¹*embedM d.radical v*(x⁻¹)⁻¹
      simp only [x,inv_inv,map_mul,map_inv]
    rw [hA₁m] at hh
    exact hh.trans (stabilizer_m_base d.radical).symm

include s in
private theorem normal_small_radius_le_slice
    (hb : 2 < replacementDistance h d)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYV : Y ≤ V d.radical (alpha d.radical))
    (hYN : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hindex : (Z d.radical (alpha d.radical)).relIndex Y ≤ 8) :
    Y ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let f := embedM d.radical
  let Y₀ := Y.comap f
  let Z₀ := (Z d.radical (alpha d.radical)).comap f
  have hg (m : d.overgroup) : f m ∈ stabilizer d.radical (alpha d.radical) := by
    change f m ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : Y₀.Normal := ⟨by
    intro v hv m
    change f (m*v*m⁻¹) ∈ Y
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hYN (hg m)) (f v)).mp hv⟩
  let : Z₀.Normal := ⟨by
    intro v hv m
    change f (m*v*m⁻¹) ∈ Z d.radical (alpha d.radical)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized d.radical _) (hg m)) (f v)).mp hv⟩
  have hVQ : V d.radical (alpha d.radical) ≤ Q d.radical (alpha d.radical) :=
    V_le_Q d.radical rfl hb
  have hYG : Y ≤ f.range := (hYV.trans ((replacementGeometry h d).V_local _ rfl hb)).trans_eq
    (stabilizer_m_base d.radical)
  have hYm : Y₀.map f = Y := map_comap_eq_self hYG
  have hZm : Z₀.map f = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  have hYker : Y₀ ≤ s.projection.ker := by
    rw [s.projection_kernel]
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [hYm,←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    exact hYV.trans hVQ
  have hk : IsPGroup 2 s.projection.ker := s.projection_kernel.symm ▸ pCore_isPGroup
  have hi : Z₀.relIndex Y₀ ≤ 8 := by
    rw [relIndex_comap,hYm]
    exact hindex
  have hh := map_mono (f := f)
    (commutator_pResidual_le_of_symmetricSix_small_section s.projection s.surjective hk Y₀ Z₀ hYker hi)
  rw [map_commutator,hYm,hZm,←Ltilde_alpha] at hh
  intro v hv
  apply (mem_B_iff d.radical _ ((replacementGeometry h d).Z_normal _)
    ((replacementGeometry h d).V_local _ rfl hb) v).mpr
  refine ⟨hYV hv,fun l hl => ?_⟩
  rw [commutator_comm] at hh
  exact hh (commutator_mem_commutator hl hv)

include s in
private theorem cube_backward_product_index (u : S)
    (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical}
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t) :
    (Z d.radical (alpha d.radical)).relIndex
      (Z d.radical c ⊔ Z d.radical (alpha d.radical)) ≤ 4 := by
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hZaQ : Z d.radical (alpha d.radical) ≤ Q d.radical (alpha d.radical) := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ rfl)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ rfl]
    exact replacementDistance_pos h d
  have hZaN : Z d.radical (alpha d.radical) ≤ normalizer
      (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    (hZaQ.trans (Q_le_adjacent_h d.radical ht hat)).trans
      ((show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c))
  let := finite_Z d.radical c
  let := finite_Z d.radical (alpha d.radical)
  rw [relIndex_sup_of_normalizes _ _ hZaN]
  exact (relIndex_le_of_le_left (adjacent_Z_le d.radical rfl hat)
    index_ne_zero_of_finite).trans_eq (cube_edge_seed_index s u hfull hcol hct)

include e hz hn in
/-- A prescribed eligible neighbor has two small critical seed candidates.
One component element relates the candidates; the chosen edge kernel
and its conjugate generate the starting stabilizer. At least one candidate fails to normalize the backward seed product. -/
theorem nonsylow_small_common_fixer_paired_seed_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          Q d.radical t ⊔ (Q d.radical t).map (MulAut.conj x).toMonoidHom =
            stabilizer d.radical (alpha d.radical) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (alpha d.radical) (act d.radical x a'),
            (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
            (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
              stabilizer d.radical (alpha d.radical) ∧
            ((¬ Z d.radical a' ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
              Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) ∨
            (¬ Z d.radical (act d.radical x a') ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
              Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))) := by
  have hb : 2 < replacementDistance h d := by omega
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,v,hparabolic,x,hxL,hxN,hx3,hgen⟩ := small_cube_common_fixer_neighbor s hc u hfull' p hsmall
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have helc : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hel
    change U d.radical (act d.radical g delta) ≤ _ at hh
    rw [U_act,←hB] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hx : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hxL
  have hfix : act d.radical x (alpha d.radical)=alpha d.radical := hx
  have hq : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (alpha d.radical) (act d.radical x a'),
      ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) := by
    have hq : ∃ q : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical x (alpha d.radical)) (act d.radical x a'),
        ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i) :=
      ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [hfix] at hq
  obtain ⟨q,hq⟩ := hq
  have hqsmall : (Q d.radical (act d.radical x a')).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    conv_lhs => rhs; rw [←hfix]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hsmall
  refine ⟨t,hat,g,hg,hgt,hct,x,hxL,hxN,hx3,q,hq,hqsmall,hgen,?_⟩
  by_contra! hboth
  apply helc
  let Y := Z d.radical c ⊔ Z d.radical (alpha d.radical)
  have hYN : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ hboth.1) hboth.2
    apply le_trans (le_inf _ _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (show Q d.radical t ≤ stabilizer d.radical c from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
    · exact (show Q d.radical t ≤ stabilizer d.radical (alpha d.radical) from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical _)
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hYV : Y ≤ V d.radical (alpha d.radical) :=
    sup_le ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
      (Z_le_VBall d.radical _ 2)
  exact (DistanceEight.U_le_Z d.radical c).trans (le_sup_left.trans
    (normal_small_radius_le_slice s hb Y hYV hYN
      ((cube_backward_product_index s u hfull' hat hct).trans (by decide))))

private theorem reverse_generating_pair {F : Type*} [Group F]
    (A K : Subgroup F) (x : F) (hx : x ∈ K)
    (hpair : A ⊔ A.map (MulAut.conj x).toMonoidHom = K) :
    A ⊔ A.map (MulAut.conj x⁻¹).toMonoidHom = K := by
  have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hpair
  have hK : K.map (MulAut.conj x⁻¹).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (K.le_normalizer (K.inv_mem hx))
  have he : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      MonoidHom.id F := by
    apply MonoidHom.ext
    intro v
    change x⁻¹*(x*v*x⁻¹)*(x⁻¹)⁻¹=v
    group
  rw [Subgroup.map_sup,map_map,he,map_id,hK] at hh
  rwa [sup_comm] at hh

include s in
/-- The common fixer for the simultaneously chosen kernels excludes the
trapped conjugate-line pair. Centrality comes from the two full kernels
generating the actual stabilizer, with no restriction on the central attachment. -/
theorem cube_common_fixer_excludes_trapped_pair
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a' b' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hps : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical (alpha d.radical))
    (q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) b')
    (hq : ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i))
    (hqs : (Q d.radical b').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hgen : Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical b' =
      stabilizer d.radical (alpha d.radical))
    (hpair : Q d.radical t ⊔ (Q d.radical t).map (MulAut.conj x).toMonoidHom =
      stabilizer d.radical (alpha d.radical))
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (hnorm : ¬ Z d.radical a' ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) : False := by
  let H := ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical (alpha d.radical)⁆
  let H' := ⁅Z d.radical c,Z d.radical b' ⊓ Q d.radical (alpha d.radical)⁆
  obtain ⟨_,_,heq,_,_,hcentral,_,hn⟩ := cube_paired_trapped_kernel_orbit s hc hb u hfull
    p hps hat hct x hx q hq hqs hgen hpbad hqbad hindex hnorm
  have hedge : H' ≤ Z d.radical t :=
    (cube_backward_kernel_le_edge_seeds s hc hb u hfull.le q hat hct hqbad).1.trans inf_le_left
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hcentral' : H' ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro v hv
    have hh := hedge hv
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hconj : H ≤ centralizer
      ((Q d.radical t).map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) := by
    change H'.map (MulAut.conj x).toMonoidHom = H at heq
    rw [←heq]
    exact (map_mono hcentral').trans (map_centralizer_le_centralizer_image _ _)
  have hfixed : H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←hpair]
    exact sup_le (le_centralizer_iff.mp hcentral) (le_centralizer_iff.mp hconj)
  exact hn (((le_centralizer_iff.mp hfixed).trans (Subgroup.centralizer_le_normalizer _)) hx)

include e hz hn in
/-- The strict source slice on the original nonsylow replacement produces
a backward critical path. The simultaneous common-fixer selection eliminates
both orientations of the trapped line pair and retains the cubic, neighbor
transporter, strict slice, and every overlapping vertex. -/
theorem nonsylow_strict_small_backward_shift_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          Q d.radical t ⊔ (Q d.radical t).map (MulAut.conj x).toMonoidHom =
            stabilizer d.radical (alpha d.radical) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (alpha d.radical) (act d.radical x a'),
            (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
            (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
              stabilizer d.radical (alpha d.radical) ∧
            let c := act d.radical g delta
            ((∃ v : CriticalPath d.radical (replacementGeometry h d) c
                (p.walk.getVert (p.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ p.walk.length-2, v.walk.getVert (i+2)=p.walk.getVert i) ∨
              (∃ v : CriticalPath d.radical (replacementGeometry h d) c
                (q.walk.getVert (q.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ q.walk.length-2, v.walk.getVert (i+2)=q.walk.getVert i)) := by
  have hb : 2 < replacementDistance h d := by omega
  have hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    have he := relIndex_eq_one.mpr hh
    omega
  obtain ⟨t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,q,hq,hqs,hgen,hnorm⟩ :=
    nonsylow_small_common_fixer_paired_seed_knownSimple (e := e) (hz := hz) (hn := hn)
      hb4 hns p hsmall hdelta hel
  let c := act d.radical g delta
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) := by
    change 2 < (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hindex
  refine ⟨t,hat,g,hg,hgt,hct,hstrict,x,hx,hxN,hx3,q,hq,hqs,hgen,?_⟩
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change color d.radical c ≠ color d.radical t at h2
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hpath {z : Vertex d.radical}
      (r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
      (hescape : ¬ Z d.radical c ≤ Q d.radical (r.walk.getVert (r.walk.length-2))) :
      ∃ v : CriticalPath d.radical (replacementGeometry h d) c (r.walk.getVert (r.walk.length-2)),
        v.walk.getVert 1=t ∧ ∀ i ≤ r.walk.length-2, v.walk.getVert (i+2)=r.walk.getVert i := by
    let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length=2 := rfl
    let v := r.prepend_two (Nat.le_of_lt hb) hcol w hw hescape
    have hvt : v.walk.getVert 1=t := by
      simp only [v,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    exact ⟨v,hvt,fun i hi => r.prepend_two_overlap _ _ _ _ _ hi⟩
  by_cases hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · by_cases hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2))
    · exfalso
      let s := fullSymmetricAction_knownSimple h e hz hn d hb
      have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
      obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
        (e := e) (hz := hz) (hn := hn) hb4 hns
      have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
        rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
      have hxG : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hx
      rcases hnorm with hnp | hnq
      · exact cube_common_fixer_excludes_trapped_pair s hc hb u hfull p hsmall hat hct
          x hxG q hq hqs hgen hxN hpbad hqbad hstrict hnp
      · have hgen' : Q d.radical t ⊔ Z d.radical (act d.radical x a') ⊔ Z d.radical a' =
            stabilizer d.radical (alpha d.radical) := by
          calc
            _ = Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') := by ac_rfl
            _ = _ := hgen
        have hqback (i : ℕ) : p.walk.getVert i = act d.radical x⁻¹ (q.walk.getVert i) := by
          rw [hq,←act_mul,mul_inv_cancel,act_one]
        exact cube_common_fixer_excludes_trapped_pair s hc hb u hfull q hqs hat hct
          x⁻¹ ((stabilizer d.radical (alpha d.radical)).inv_mem hxG) p hqback hsmall hgen'
          (reverse_generating_pair _ _ x hxG hxN) hqbad hpbad hstrict hnq
    · exact Or.inr (hpath q hqbad)
  · exact Or.inl (hpath p hpbad)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
