import data.stream.basic
import tactic.norm_num

namespace padovan

private def padovan_aux_step : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) := λ t, ⟨t.2.1, t.2.2, t.1 + t.2.1⟩

private def padovan_aux_stream : stream (ℕ × ℕ × ℕ) := stream.iterate padovan_aux_step ⟨1, 1, 1⟩

def padovan (n : ℕ) : ℕ := (padovan_aux_stream n).1

@[simp] lemma padovan_zero : padovan 0 = 1 := rfl
@[simp] lemma padovan_one : padovan 1 = 1 := rfl
@[simp] lemma padovan_two : padovan 2 = 1 := rfl

private lemma padovan_aux_stream_succ {n : ℕ} :
    padovan_aux_stream (n + 1) = padovan_aux_step (padovan_aux_stream n) :=
begin
  change (stream.nth (n + 1) $ stream.iterate padovan_aux_step ⟨1, 1, 1⟩) =
      padovan_aux_step (stream.nth n $ stream.iterate padovan_aux_step ⟨1, 1, 1⟩),
  rw [stream.nth_succ_iterate, stream.map_iterate, stream.nth_map],
end

lemma padovan_succ_succ_succ {n : ℕ} : padovan (n + 3) = padovan n + padovan (n + 1) :=
by simp only [padovan, padovan_aux_stream_succ, padovan_aux_step]

lemma padovan_pos (n : ℕ) : 0 < padovan n :=
begin
  induction n with k nk,
  norm_num,
  sorry
end

end padovan
