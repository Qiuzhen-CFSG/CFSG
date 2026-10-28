module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.SourceMaps
public import Theory.GroupTheory.CosetWordCertificate.Tietze
/-!
# The actual binary Ree endpoint relations in every faithful completion

The second endpoint's Weyl involution conjugates the two radical generators to
specified Sylow elements and braids with the remaining involution. These
relations reduce every second-endpoint word to a finite Sylow-group identity.
Together with the first endpoint calculation this verifies the exact local
relations used by the bad-braid certificates, along the original overlap maps.

Source: Aschbacher–Smith F.4.4 and F.4.8; Shinoda's marked binary Ree parabolics.
-/
@[expose] public section
noncomputable section
namespace Tits.AmalgamRigidity.FullRee.BadBraid
open ReeTwo Subgroup.CosetWordCertificate
variable {G : Type*} [Group G]
private theorem map_eval {H α : Type*} [Group H] (f : H →* G) (g : α → H)
    (w : Word α) : f (eval g w) = eval (fun i => f (g i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons, map_mul, ih, eval_cons]
    congr 1
    cases a.2 <;> simp

theorem source_weyl_relations (c : Completion (G := G)) :
    SecondExtension.WeylRelations (middleMap c) (generator c 4) where
  square := by
    change c.right SecondExtension.reflection ^ 2 = 1
    rw [← map_pow, SecondExtension.weyl_relations.square, map_one]
  cube := by
    rw [middle_right]
    change (c.right (SecondExtension.inclusion (SylowModel.root 0)) *
      c.right SecondExtension.reflection) ^ 3 = 1
    rw [← map_mul, ← map_pow, SecondExtension.weyl_relations.cube, map_one]
  conjugate i := by
    rw [middle_right, middle_right]
    change c.right SecondExtension.reflection * c.right (SecondExtension.inclusion _) *
      (c.right SecondExtension.reflection)⁻¹ = c.right (SecondExtension.inclusion _)
    rw [← map_inv, ← map_mul, ← map_mul, SecondExtension.weyl_relations.conjugate]

private def radSource : Fin 2 → SylowModel := ![SylowModel.rootOne, SylowModel.root 2]
private def radTarget : Fin 2 → SylowModel := ![SylowModel.root 1, SylowModel.root 3]
private def sourceIndex : Fin 2 → Nat := ![0,2]
private def targetIndex : Fin 2 → Nat := ![5,6]

private theorem conjugate_word (c : Completion (G := G))
    (pre : Word Nat) (w : Word (Fin 2)) (post : Word Nat) :
    eval (generator c) (pre ++ [(4,true)] ++
      w.map (fun a => (sourceIndex a.1,a.2)) ++ [(4,true)] ++ post) =
    eval (generator c) (pre ++ w.map (fun a => (targetIndex a.1,a.2)) ++ post) := by
  let s := generator c 4
  let f := middleMap c
  have hi : s⁻¹ = s := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using (source_weyl_relations c).square)
  have he : ∀ i, (MulAut.conj s) (f (radSource i)) = f (radTarget i) := by
    intro i
    fin_cases i
    · exact (source_weyl_relations c).conjugate 0
    · exact (source_weyl_relations c).conjugate 2
  have hconj : s * f (eval radSource w) * s = f (eval radTarget w) := by
    calc
      _ = (MulAut.conj s) (f (eval radSource w)) := by rw [MulAut.conj_apply, hi]
      _ = eval (fun i => (MulAut.conj s) (f (radSource i))) w := by
        rw [map_eval]
        exact map_eval (MulAut.conj s).toMonoidHom _ _
      _ = eval (fun i => f (radTarget i)) w := by simp only [he]
      _ = _ := (map_eval f radTarget w).symm
  have hsrc : eval (generator c) (w.map (fun a => (sourceIndex a.1,a.2))) =
      f (eval radSource w) := by
    rw [eval_map_letters, map_eval]
    congr 1
    funext i
    fin_cases i <;> rfl
  have htar : eval (generator c) (w.map (fun a => (targetIndex a.1,a.2))) =
      f (eval radTarget w) := by
    rw [eval_map_letters, map_eval]
    congr 1
    funext i
    fin_cases i <;> rfl
  simpa only [eval_append, eval_letter, Bool.true_eq, ↓reduceIte, hsrc, htar,
    mul_assoc] using congrArg (fun z => eval (generator c) pre * z *
      eval (generator c) post) hconj

private theorem braid_word (c : Completion (G := G)) (pre post : Word Nat) :
    eval (generator c) (pre ++ [(1,true),(4,true),(1,true)] ++ post) =
    eval (generator c) (pre ++ [(4,true),(1,true),(4,true)] ++ post) := by
  let x := generator c 1
  let s := generator c 4
  have hx : x ^ 2 = 1 := by
    change middleMap c (SylowModel.root 0) ^ 2 = 1
    rw [← map_pow, (by decide +kernel : SylowModel.root 0 ^ 2 = 1), map_one]
  have hs := (source_weyl_relations c).square
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  have hm : (x*s*x)*(s*x*s)=1 := by
    simpa only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using (show (x*s)^3=1 from (source_weyl_relations c).cube)
  have hb : x*s*x=s*x*s := (eq_inv_of_mul_eq_one_left hm).trans
    (by simp only [mul_inv_rev,hxi,hsi,mul_assoc])
  simpa only [eval_append,eval_cons,eval_nil,Bool.true_eq,↓reduceIte,mul_one,mul_assoc] using
    congrArg (fun z => eval (generator c) pre * z * eval (generator c) post) hb

def sylowGenerator : Nat → SylowModel
 | 0 => SylowModel.rootOne
 | 1 => SylowModel.root 0
 | 2 => SylowModel.root 2
 | 5 => SylowModel.root 1
 | 6 => SylowModel.root 3
 | _ => 1

def collected : Fin 17 → Word Nat := ![
[(1, true), (1, true)],
[],
[(0, true), (2, false), (0, false), (2, true)],
[(0, true), (0, true), (0, true), (0, true)],
[(2, true), (2, true), (2, true), (2, true)],
[(2, false), (1, true), (2, true), (2, true), (1, true), (2, false)],
[],
[(1, true), (2, true), (5, false), (5, false), (1, true), (2, false)],
[(1, true), (5, true), (1, true), (5, false)],
[(0, false), (6, false), (5, false), (0, true), (2, true), (5, true)],
[(1, true), (6, true), (0, false), (1, true), (0, true), (2, false), (1, true), (2, false), (0, true), (1, true), (0, false), (2, false)],
[(1, true), (0, true), (0, true), (2, false), (1, true), (0, false), (2, true), (1, true), (2, false), (6, false), (1, true), (0, false)],
[(1, true), (2, true), (1, true), (0, true), (1, true), (2, false), (0, true), (1, true), (0, false), (1, true), (2, false), (0, true), (1, true), (0, false), (2, true), (0, false)],
[(2, true), (5, true), (2, true), (5, true), (2, false), (5, false), (2, false), (5, false)],
[(1, true), (0, false), (2, false), (1, true), (0, false), (5, false), (2, false), (5, true), (0, true), (1, true), (0, true), (2, false), (1, true), (2, false)],
[(0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (2, false), (1, true), (0, false), (0, false), (5, false), (2, false), (2, false)],
[(0, true), (1, true), (0, false), (2, true), (1, true), (0, false), (5, false), (0, true), (0, true), (1, true), (2, true), (0, false), (1, true), (0, false), (5, false), (0, true)]]
theorem collected_relations : ∀ i : Fin 17, eval sylowGenerator (collected i) = 1 := by
  decide +kernel
private theorem eval_congr_on {g h : Nat → G} (w : Word Nat)
    (he : ∀ a ∈ w, g a.1 = h a.1) : eval g w = eval h w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [eval_cons, eval_cons, he a (List.mem_cons_self ..),
      ih (fun z hz => he z (List.mem_cons_of_mem _ hz))]
private theorem collected_source (c : Completion (G := G)) (i : Fin 17) :
    eval (generator c) (collected i) = 1 := by
  have he := congrArg (middleMap c) (collected_relations i)
  rw [map_eval, map_one] at he
  refine (eval_congr_on _ ?_).trans he
  intro a ha
  have hb : a.1 < 7 ∧ a.1 ≠ 3 ∧ a.1 ≠ 4 :=
    (by decide +kernel : ∀ i : Fin 17, ∀ a ∈ collected i,
      a.1 < 7 ∧ a.1 ≠ 3 ∧ a.1 ≠ 4) i a ha
  rcases a with ⟨j,b⟩
  dsimp at hb ⊢
  obtain ⟨hj,hj3,hj4⟩ := hb
  interval_cases j <;> simp_all [generator,sylowGenerator]

private theorem row22 (c : Completion (G := G)) : eval (generator c) (relator 22) = 1 := by
  calc
    _ = 1 := collected_source c 0

private theorem row23 (c : Completion (G := G)) : eval (generator c) (relator 23) = 1 := by
  change eval (generator c) [(4,true),(4,true)] = 1
  simpa only [eval_cons,eval_nil,Bool.true_eq,↓reduceIte,mul_one,pow_two] using (source_weyl_relations c).square

private theorem row24 (c : Completion (G := G)) : eval (generator c) (relator 24) = 1 := by
  calc
    _ = 1 := collected_source c 2

private theorem row25 (c : Completion (G := G)) : eval (generator c) (relator 25) = 1 := by
  calc
    _ = 1 := collected_source c 3

private theorem row26 (c : Completion (G := G)) : eval (generator c) (relator 26) = 1 := by
  calc
    _ = 1 := collected_source c 4

private theorem row27 (c : Completion (G := G)) : eval (generator c) (relator 27) = 1 := by
  calc
    _ = 1 := collected_source c 5

private theorem row28 (c : Completion (G := G)) : eval (generator c) (relator 28) = 1 := by
  let s := generator c 4
  let x := generator c 1
  have he : (MulAut.conj s) (x*s) = s*x := by simp only [MulAut.conj_apply]; group
  have hc0 : (x*s)^3=1 := (source_weyl_relations c).cube
  have hc : (s*x)^3=1 := by
    rw [←he,←map_pow,hc0,map_one]
  change eval (generator c) [(4,true),(1,true),(4,true),(1,true),(4,true),(1,true)] = 1
  simpa only [eval_cons,eval_nil,Bool.true_eq,↓reduceIte,mul_one,one_mul,pow_succ,pow_zero,mul_assoc] using hc

private theorem row29 (c : Completion (G := G)) : eval (generator c) (relator 29) = 1 := by
  calc
    _ = eval (generator c) [(1, true), (2, true), (5, false), (5, false), (1, true), (2, false)] := by
      exact conjugate_word c [(1, true), (2, true)] [(0, false), (0, false)] [(1, true), (2, false)]
    _ = 1 := collected_source c 7

private theorem row30 (c : Completion (G := G)) : eval (generator c) (relator 30) = 1 := by
  calc
    _ = eval (generator c) [(1, true), (4, true), (0, true), (4, true), (1, true), (4, true), (0, false), (4, true)] := by
      exact braid_word c [(1, true), (4, true), (0, true)] [(0, false), (4, true)]
    _ = eval (generator c) [(1, true), (5, true), (1, true), (4, true), (0, false), (4, true)] := by
      exact conjugate_word c [(1, true)] [(0, true)] [(1, true), (4, true), (0, false), (4, true)]
    _ = eval (generator c) [(1, true), (5, true), (1, true), (5, false)] := by
      exact conjugate_word c [(1, true), (5, true), (1, true)] [(0, false)] []
    _ = 1 := collected_source c 8

private theorem row31 (c : Completion (G := G)) : eval (generator c) (relator 31) = 1 := by
  calc
    _ = eval (generator c) [(0, false), (6, false), (5, false), (0, true), (2, true), (4, true), (0, true), (4, true)] := by
      exact conjugate_word c [(0, false)] [(1, false), (0, false)] [(0, true), (2, true), (4, true), (0, true), (4, true)]
    _ = eval (generator c) [(0, false), (6, false), (5, false), (0, true), (2, true), (5, true)] := by
      exact conjugate_word c [(0, false), (6, false), (5, false), (0, true), (2, true)] [(0, true)] []
    _ = 1 := collected_source c 9

private theorem row32 (c : Completion (G := G)) : eval (generator c) (relator 32) = 1 := by
  calc
    _ = eval (generator c) [(1, true), (6, true), (0, false), (1, true), (0, true), (2, false), (1, true), (2, false), (0, true), (1, true), (0, false), (2, false)] := by
      exact conjugate_word c [(1, true)] [(1, true)] [(0, false), (1, true), (0, true), (2, false), (1, true), (2, false), (0, true), (1, true), (0, false), (2, false)]
    _ = 1 := collected_source c 10

private theorem row33 (c : Completion (G := G)) : eval (generator c) (relator 33) = 1 := by
  calc
    _ = eval (generator c) [(1, true), (0, true), (0, true), (2, false), (1, true), (0, false), (2, true), (1, true), (2, false), (6, false), (1, true), (0, false)] := by
      exact conjugate_word c [(1, true), (0, true), (0, true), (2, false), (1, true), (0, false), (2, true), (1, true), (2, false)] [(1, false)] [(1, true), (0, false)]
    _ = 1 := collected_source c 11

private theorem row34 (c : Completion (G := G)) : eval (generator c) (relator 34) = 1 := by
  calc
    _ = 1 := collected_source c 12

private theorem row35 (c : Completion (G := G)) : eval (generator c) (relator 35) = 1 := by
  calc
    _ = eval (generator c) [(2, true), (5, true), (2, true), (4, true), (0, true), (4, true), (2, false), (4, true), (0, false), (4, true), (2, false), (4, true), (0, false), (4, true)] := by
      exact conjugate_word c [(2, true)] [(0, true)] [(2, true), (4, true), (0, true), (4, true), (2, false), (4, true), (0, false), (4, true), (2, false), (4, true), (0, false), (4, true)]
    _ = eval (generator c) [(2, true), (5, true), (2, true), (5, true), (2, false), (4, true), (0, false), (4, true), (2, false), (4, true), (0, false), (4, true)] := by
      exact conjugate_word c [(2, true), (5, true), (2, true)] [(0, true)] [(2, false), (4, true), (0, false), (4, true), (2, false), (4, true), (0, false), (4, true)]
    _ = eval (generator c) [(2, true), (5, true), (2, true), (5, true), (2, false), (5, false), (2, false), (4, true), (0, false), (4, true)] := by
      exact conjugate_word c [(2, true), (5, true), (2, true), (5, true), (2, false)] [(0, false)] [(2, false), (4, true), (0, false), (4, true)]
    _ = eval (generator c) [(2, true), (5, true), (2, true), (5, true), (2, false), (5, false), (2, false), (5, false)] := by
      exact conjugate_word c [(2, true), (5, true), (2, true), (5, true), (2, false), (5, false), (2, false)] [(0, false)] []
    _ = 1 := collected_source c 13

private theorem row36 (c : Completion (G := G)) : eval (generator c) (relator 36) = 1 := by
  calc
    _ = eval (generator c) [(1, true), (0, false), (2, false), (1, true), (0, false), (5, false), (2, false), (4, true), (0, true), (4, true), (0, true), (1, true), (0, true), (2, false), (1, true), (2, false)] := by
      exact conjugate_word c [(1, true), (0, false), (2, false), (1, true), (0, false)] [(0, false)] [(2, false), (4, true), (0, true), (4, true), (0, true), (1, true), (0, true), (2, false), (1, true), (2, false)]
    _ = eval (generator c) [(1, true), (0, false), (2, false), (1, true), (0, false), (5, false), (2, false), (5, true), (0, true), (1, true), (0, true), (2, false), (1, true), (2, false)] := by
      exact conjugate_word c [(1, true), (0, false), (2, false), (1, true), (0, false), (5, false), (2, false)] [(0, true)] [(0, true), (1, true), (0, true), (2, false), (1, true), (2, false)]
    _ = 1 := collected_source c 14

private theorem row37 (c : Completion (G := G)) : eval (generator c) (relator 37) = 1 := by
  calc
    _ = eval (generator c) [(0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (2, false), (1, true), (0, false), (0, false), (5, false), (2, false), (2, false)] := by
      exact conjugate_word c [(0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (2, false), (1, true), (0, false), (0, false)] [(0, false)] [(2, false), (2, false)]
    _ = 1 := collected_source c 15

private theorem row38 (c : Completion (G := G)) : eval (generator c) (relator 38) = 1 := by
  calc
    _ = eval (generator c) [(0, true), (1, true), (0, false), (2, true), (1, true), (0, false), (5, false), (0, true), (0, true), (1, true), (2, true), (0, false), (1, true), (0, false), (4, true), (0, false), (4, true), (0, true)] := by
      exact conjugate_word c [(0, true), (1, true), (0, false), (2, true), (1, true), (0, false)] [(0, false)] [(0, true), (0, true), (1, true), (2, true), (0, false), (1, true), (0, false), (4, true), (0, false), (4, true), (0, true)]
    _ = eval (generator c) [(0, true), (1, true), (0, false), (2, true), (1, true), (0, false), (5, false), (0, true), (0, true), (1, true), (2, true), (0, false), (1, true), (0, false), (5, false), (0, true)] := by
      exact conjugate_word c [(0, true), (1, true), (0, false), (2, true), (1, true), (0, false), (5, false), (0, true), (0, true), (1, true), (2, true), (0, false), (1, true), (0, false)] [(0, false)] [(0, true)]
    _ = 1 := collected_source c 16

theorem second_source_relations (c : Completion (G := G)) (i : Fin 17) :
    eval (generator c) (relator ⟨i.val+22,by omega⟩) = 1 := by
  fin_cases i
  · exact row22 c
  · exact row23 c
  · exact row24 c
  · exact row25 c
  · exact row26 c
  · exact row27 c
  · exact row28 c
  · exact row29 c
  · exact row30 c
  · exact row31 c
  · exact row32 c
  · exact row33 c
  · exact row34 c
  · exact row35 c
  · exact row36 c
  · exact row37 c
  · exact row38 c

theorem source_relations (c : Completion (G := G)) (i : Fin 39) :
    eval (generator c) (relator i) = 1 := by
  by_cases hi : i.val < 22
  · exact first_source_relations c ⟨i.val,hi⟩
  · have he := second_source_relations c ⟨i.val-22,by omega⟩
    convert he using 1
    congr 2
    apply Fin.ext
    dsimp
    omega
end Tits.AmalgamRigidity.FullRee.BadBraid
